/* 5FYJ Env trimer that turns with scroll, with a bound Fab that changes with the page section.
   GPU (WebGL2) renderer: Env and Fab are depth-buffered, banded-shaded sphere impostors that merge into a continuous
   surface, with contour lines found from the depth buffer; Man9 glycans are thin ball-and-stick branches.
   Falls back to the CPU renderer (env-viewer-cpu.js) when WebGL2 is not available.
   Public API: window.EnvViewer.setFab('pgt122' | 'vrc01' | 'o22' | null) */
(function(){
  var C=window.ENV5FYJ,fig=document.getElementById('envFig'),cv=document.getElementById('envCanvas');
  if(!C||!fig||!cv)return;
  var api=window.EnvViewer={_req:null,setFab:function(k){api._req=k||null}};

  function fallback(why){
    if(why)console.warn('Env viewer: using CPU renderer ('+why+')');
    var nc=cv.cloneNode(false);cv.parentNode.replaceChild(nc,cv);
    var s=document.createElement('script');s.src='assets/env-viewer-cpu.js?v=11';document.head.appendChild(s);
  }
  var probe=document.createElement('canvas'),ok=false;
  try{ok=!!probe.getContext('webgl2')}catch(e){}
  if(!ok||!window.DecompressionStream){fallback('no WebGL2');return}

  var H=C.h,FH=C.fh;
  var VDW=[1.7,1.55,1.52,1.8];
  var PROBE=0.13,BALL=0.10,STICK=0.07,EDGE_THR=0.30;                        /* nm */
  var PAL=[[0,0,0],[232,229,223],[226,223,217],[220,217,211],[238,168,148],[164,204,220],[190,200,234]];
  var OUT_SIL=[84,142,134],OUT_IN=[70,76,138];
  var LX=-0.42,LY=0.52,LZ=0.74;{var ll=Math.hypot(LX,LY,LZ);LX/=ll;LY/=ll;LZ/=ll}

  var gl=null,prog=null,post=null,U={},UP={},ready=false;
  var W=0,Hh=0,DPRc=1.5,cw=0,ch=0,scale=1,ext=28,fbo=null,texC=null,texD=null,vaoEmpty=null;
  var prot=null,fabs={},gly=null,hidden={},hidKey='~',want=null;
  var pitch=0.28,yawCur=null,dirty=true,wasMoving=false,last=performance.now();

  var VS='#version 300 es\n'+
  'in vec3 aPos;in float aRad;in float aCls;\n'+
  'uniform vec4 uRot;uniform vec3 uOff;uniform float uScale;uniform vec2 uVP;uniform vec3 uPal[7];\n'+
  'out float vZ;out float vR;out vec3 vBase;\n'+
  'void main(){vec3 p=aPos+uOff;\n'+
  ' float xs=p.x*uRot.x-p.y*uRot.y;float d0=p.x*uRot.y+p.y*uRot.x;\n'+
  ' float ys=p.z*uRot.z-d0*uRot.w;float zs=p.z*uRot.w+d0*uRot.z;\n'+
  ' vZ=zs;vR=aRad;vBase=uPal[int(aCls+0.5)];\n'+
  ' gl_Position=vec4(xs*uScale*2.0/uVP.x,ys*uScale*2.0/uVP.y,0.0,1.0);\n'+
  ' gl_PointSize=2.0*aRad*uScale;}';
  var FS='#version 300 es\nprecision highp float;\n'+
  'in float vZ;in float vR;in vec3 vBase;\n'+
  'uniform float uZR;uniform float uCue;uniform vec3 uLight;uniform float uFlag;\n'+
  'out vec4 oC;\n'+
  'void main(){vec2 pc=gl_PointCoord*2.0-1.0;pc.y=-pc.y;float d2=dot(pc,pc);if(d2>1.0)discard;\n'+
  ' float nz=sqrt(1.0-d2);float zz=vZ+nz*vR;\n'+
  ' gl_FragDepth=clamp(0.5-zz/(2.0*uZR),0.0,1.0);\n'+
  ' float L=max(dot(vec3(pc,nz),uLight),0.0);float b=min(4.0,floor(L*5.0));\n'+
  ' float u=clamp((zz+uCue)/(2.0*uCue),0.0,1.0);float dl=min(3.0,floor(u*4.0));\n'+
  ' float f=(0.78+0.22*b/4.0)*(0.90+0.10*dl/3.0);\n'+
  ' oC=vec4(vBase*f,uFlag>0.5?0.99:1.0);}';
  var PVS='#version 300 es\nvoid main(){vec2 v=vec2(float((gl_VertexID<<1)&2),float(gl_VertexID&2));gl_Position=vec4(v*2.0-1.0,0.0,1.0);}';
  var PFS='#version 300 es\nprecision highp float;precision highp int;\n'+
  'uniform sampler2D uC;uniform sampler2D uD;uniform int uT;uniform float uThr;uniform float uFadeW;uniform vec3 uSil;uniform vec3 uInn;\n'+
  'out vec4 o;\n'+
  'void main(){ivec2 p=ivec2(gl_FragCoord.xy);ivec2 sz=textureSize(uC,0);\n'+
  ' float d=texelFetch(uD,p,0).r;if(d>=0.99999){o=vec4(0.0);return;}\n'+
  ' float fd=smoothstep(0.0,uFadeW,float(min(p.x,sz.x-1-p.x)))*smoothstep(0.0,uFadeW,float(min(p.y,sz.y-1-p.y)));\n'+
  ' vec4 c=texelFetch(uC,p,0);if(c.a<0.995){o=vec4(c.rgb*fd,fd);return;}\n'+
  ' int e=0;ivec2 offs[4]=ivec2[4](ivec2(uT,0),ivec2(-uT,0),ivec2(0,uT),ivec2(0,-uT));\n'+
  ' for(int i=0;i<4;i++){ivec2 q=p+offs[i];\n'+
  '  if(q.x<0||q.y<0||q.x>=sz.x||q.y>=sz.y){e=1;continue;}\n'+
  '  float dn=texelFetch(uD,q,0).r;\n'+
  '  if(dn>=0.99999){e=1;}else if(e==0&&d-dn>uThr){if(texelFetch(uC,q,0).a>0.995)e=2;}}\n'+
  ' vec3 col=(e==1)?uSil:((e==2)?uInn:c.rgb);o=vec4(col*fd,fd);}';

  function sh(type,src){var s=gl.createShader(type);gl.shaderSource(s,src);gl.compileShader(s);
    if(!gl.getShaderParameter(s,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(s));return s}
  function program(vs,fs){var p=gl.createProgram();gl.attachShader(p,sh(gl.VERTEX_SHADER,vs));gl.attachShader(p,sh(gl.FRAGMENT_SHADER,fs));
    gl.linkProgram(p);if(!gl.getProgramParameter(p,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(p));return p}
  function locs(p,names){var o={};names.forEach(function(n){o[n]=gl.getUniformLocation(p,n)});return o}

  function b64(b){var s=atob(b),a=new Uint8Array(s.length);for(var i=0;i<s.length;i++)a[i]=s.charCodeAt(i);return a}
  async function inflate(b){var st=new Blob([b64(b)]).stream().pipeThrough(new DecompressionStream('gzip'));return await new Response(st).arrayBuffer()}

  /* a point buffer with its own VAO: [x,y,z,radius,class] per point */
  function makeSet(arr,count,dynamic){
    var vao=gl.createVertexArray(),vbo=gl.createBuffer();gl.bindVertexArray(vao);gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bufferData(gl.ARRAY_BUFFER,arr,dynamic?gl.DYNAMIC_DRAW:gl.STATIC_DRAW);
    var st=20;gl.enableVertexAttribArray(0);gl.vertexAttribPointer(0,3,gl.FLOAT,false,st,0);
    gl.enableVertexAttribArray(1);gl.vertexAttribPointer(1,1,gl.FLOAT,false,st,12);
    gl.enableVertexAttribArray(2);gl.vertexAttribPointer(2,1,gl.FLOAT,false,st,16);
    gl.bindVertexArray(null);return {vao:vao,vbo:vbo,n:count};
  }

  async function load(){
    var buf=await inflate(C.d1),o=0;
    var i16=function(n){var a=new Int16Array(buf,o,n*3);o+=n*6;return a};
    var P=i16(H.nP),Gl=i16(H.nG);i16(H.nPB);i16(H.nGB);
    var u8=function(n){var a=new Uint8Array(buf,o,n);o+=n;return a};
    var Pe=u8(H.nP),Pp=u8(H.nP);u8(H.nG);u8(H.nPB);u8(H.nG);u8(H.nP);var Gs=u8(H.nG);
    var b2=await inflate(C.d2),o2=0;
    var zmin=1e9,zmax=-1e9,gr=0,i;
    for(i=0;i<H.nP;i++){var z=P[i*3+2]/100;if(z<zmin)zmin=z;if(z>zmax)zmax=z}
    for(i=0;i<H.nG;i++){var g=Math.hypot(Gl[i*3]/100,Gl[i*3+1]/100);if(g>gr)gr=g}
    var height=zmax-zmin,zc=height/2,gw=2*gr;
    var pa=new Float32Array(H.nP*5);
    for(i=0;i<H.nP;i++){pa[i*5]=-P[i*3]/100;pa[i*5+1]=P[i*3+1]/100;pa[i*5+2]=P[i*3+2]/100-zmin-zc;pa[i*5+3]=VDW[Pe[i]]/10+PROBE;pa[i*5+4]=Pp[i]+1}
    prot=makeSet(pa,H.nP,false);
    ext=Math.max(height+2,gw)*1.05;
    FH.forEach(function(h){
      var P2=new Int16Array(b2,o2,h.n*3);o2+=h.n*6;var e=new Uint8Array(b2,o2,h.n);o2+=h.n;var c=new Uint8Array(b2,o2,h.n);o2+=h.n;
      var fa=new Float32Array(h.n*5),cx=0,cy=0,rb=0,j;
      for(j=0;j<h.n;j++){var x=-P2[j*3]/100,y=P2[j*3+1]/100,zz=P2[j*3+2]/100-zmin-zc;
        fa[j*5]=x;fa[j*5+1]=y;fa[j*5+2]=zz;fa[j*5+3]=VDW[e[j]]/10+PROBE;fa[j*5+4]=c[j]?6:5;cx+=x;cy+=y;rb=Math.max(rb,Math.sqrt(x*x+y*y+zz*zz))}
      cx/=h.n;cy/=h.n;
      ext=Math.max(ext,2*Math.max(rb+0.2,Math.hypot(gw/2,height/2))*1.04);
      var set=makeSet(fa,h.n,false);set.n=h.n;set.phi=Math.atan2(cy,cx);set.t=0;set.e=0;set.raw=P2;set.rb=rb;fabs[h.k]=set;
    });
    /* glycans: atoms plus points along every covalent bond (heavy-atom distance < 1.9 A) */
    var cell=1.9,grid={},bonds=[],j2,k,key;
    for(i=0;i<H.nG;i++){key=Math.floor(Gl[i*3]/10/cell)+','+Math.floor(Gl[i*3+1]/10/cell)+','+Math.floor(Gl[i*3+2]/10/cell);(grid[key]||(grid[key]=[])).push(i)}
    for(i=0;i<H.nG;i++){
      var ax=Gl[i*3]/10,ay=Gl[i*3+1]/10,az=Gl[i*3+2]/10,ix=Math.floor(ax/cell),iy=Math.floor(ay/cell),iz=Math.floor(az/cell);
      for(var a=-1;a<2;a++)for(var b=-1;b<2;b++)for(var c2=-1;c2<2;c2++){
        var L=grid[(ix+a)+','+(iy+b)+','+(iz+c2)];if(!L)continue;
        for(k=0;k<L.length;k++){j2=L[k];if(j2<=i)continue;
          var dx=Gl[j2*3]/10-ax,dy=Gl[j2*3+1]/10-ay,dz=Gl[j2*3+2]/10-az;
          if(dx*dx+dy*dy+dz*dz<3.61)bonds.push(i,j2)}}}
    var gx=function(i){return -Gl[i*3]/100},gy=function(i){return Gl[i*3+1]/100},gz=function(i){return Gl[i*3+2]/100-zmin-zc};
    var STICKPTS=3,n=H.nG+bonds.length/2*STICKPTS,pts=new Float32Array(n*4),site=new Uint16Array(n),m=0;
    for(i=0;i<H.nG;i++){pts[m*4]=gx(i);pts[m*4+1]=gy(i);pts[m*4+2]=gz(i);pts[m*4+3]=BALL;site[m]=Gs[i];m++}
    for(k=0;k<bonds.length;k+=2){var s1=bonds[k],s2=bonds[k+1];
      for(var q=1;q<=STICKPTS;q++){var tt=q/(STICKPTS+1);
        pts[m*4]=gx(s1)+(gx(s2)-gx(s1))*tt;pts[m*4+1]=gy(s1)+(gy(s2)-gy(s1))*tt;pts[m*4+2]=gz(s1)+(gz(s2)-gz(s1))*tt;pts[m*4+3]=STICK;site[m]=Gs[s1];m++}}
    gly={pts:pts,site:site,n:m,Graw:Gl,Gs:Gs,set:null};
    gly.set=makeSet(new Float32Array(5),0,true);
    uploadGlycans({});
    ready=true;
  }

  function uploadGlycans(hide){
    var src=gly.pts,site=gly.site,out=new Float32Array(gly.n*5),m=0;
    for(var i=0;i<gly.n;i++){if(hide[site[i]])continue;
      out[m*5]=src[i*4];out[m*5+1]=src[i*4+1];out[m*5+2]=src[i*4+2];out[m*5+3]=src[i*4+3];out[m*5+4]=4;m++}
    gl.bindBuffer(gl.ARRAY_BUFFER,gly.set.vbo);gl.bufferData(gl.ARRAY_BUFFER,out.subarray(0,m*5),gl.DYNAMIC_DRAW);gly.set.n=m;
  }

  /* glycans that sit where the Fab binds are hidden, as in the report */
  function clashSet(key){
    var set={};if(!key)return set;
    var F=fabs[key],Cc=2.8,grid={},j,k,G=gly.Graw,Gs=gly.Gs;
    for(j=0;j<F.n;j++){var x=F.raw[j*3]/10,y=F.raw[j*3+1]/10,z=F.raw[j*3+2]/10,kk=Math.floor(x/Cc)+','+Math.floor(y/Cc)+','+Math.floor(z/Cc);(grid[kk]||(grid[kk]=[])).push([x,y,z])}
    for(k=0;k<H.nG;k++){
      var X=G[k*3]/10,Y=G[k*3+1]/10,Zz=G[k*3+2]/10,ix=Math.floor(X/Cc),iy=Math.floor(Y/Cc),iz=Math.floor(Zz/Cc),hit=false;
      if(set[Gs[k]])continue;
      for(var a=-1;a<2&&!hit;a++)for(var b=-1;b<2&&!hit;b++)for(var c=-1;c<2&&!hit;c++){
        var L=grid[(ix+a)+','+(iy+b)+','+(iz+c)];if(!L)continue;
        for(var qq=0;qq<L.length;qq++){var dx=L[qq][0]-X,dy=L[qq][1]-Y,dz=L[qq][2]-Zz;if(dx*dx+dy*dy+dz*dz<Cc*Cc){hit=true;break}}}
      if(hit)set[Gs[k]]=1}
    return set;
  }

  function makeTargets(){
    if(texC){gl.deleteTexture(texC);gl.deleteTexture(texD)}
    texC=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,texC);
    gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA8,cw,ch,0,gl.RGBA,gl.UNSIGNED_BYTE,null);
    gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.NEAREST);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.NEAREST);
    texD=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,texD);
    gl.texImage2D(gl.TEXTURE_2D,0,gl.DEPTH_COMPONENT24,cw,ch,0,gl.DEPTH_COMPONENT,gl.UNSIGNED_INT,null);
    gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.NEAREST);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.NEAREST);
    gl.bindFramebuffer(gl.FRAMEBUFFER,fbo);
    gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.COLOR_ATTACHMENT0,gl.TEXTURE_2D,texC,0);
    gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.DEPTH_ATTACHMENT,gl.TEXTURE_2D,texD,0);
    gl.bindFramebuffer(gl.FRAMEBUFFER,null);
  }

  function size(){
    var r=fig.getBoundingClientRect();W=Math.max(1,Math.round(r.width));Hh=Math.max(1,Math.round(r.height));
    DPRc=Math.max(1.5,Math.min(window.devicePixelRatio||1,2));
    cw=Math.round(W*DPRc);ch=Math.round(Hh*DPRc);cv.width=cw;cv.height=ch;
    if(gl&&fbo)makeTargets();
    scale=Math.min(W,Hh)/ext*1.05;dirty=true;
  }

  function drawSet(s,off,flag){
    if(!s.n)return;gl.uniform3f(U.uOff,off[0],off[1],off[2]);gl.uniform1f(U.uFlag,flag);
    gl.bindVertexArray(s.vao);gl.drawArrays(gl.POINTS,0,s.n);
  }
  function render(){
    var zr=ext*0.5+2;
    gl.bindFramebuffer(gl.FRAMEBUFFER,fbo);gl.viewport(0,0,cw,ch);
    gl.clearColor(0,0,0,0);gl.clearDepth(1);gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LESS);gl.depthMask(true);gl.disable(gl.BLEND);
    gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);
    gl.useProgram(prog);
    gl.uniform4f(U.uRot,Math.cos(yawCur),Math.sin(yawCur),Math.cos(pitch),Math.sin(pitch));
    gl.uniform1f(U.uScale,scale*DPRc);gl.uniform2f(U.uVP,cw,ch);
    gl.uniform1f(U.uZR,zr);gl.uniform1f(U.uCue,11);gl.uniform3f(U.uLight,LX,LY,LZ);
    drawSet(prot,[0,0,0],0);
    for(var k in fabs){var F=fabs[k];if(F.e<0.01)continue;var d=(1-F.e)*7;drawSet(F,[Math.cos(F.phi)*d,Math.sin(F.phi)*d,0],0)}
    drawSet(gly.set,[0,0,0],1);
    /* contour pass: outlines from the depth buffer */
    gl.bindFramebuffer(gl.FRAMEBUFFER,null);gl.viewport(0,0,cw,ch);gl.disable(gl.DEPTH_TEST);gl.clearColor(0,0,0,0);gl.clear(gl.COLOR_BUFFER_BIT);
    gl.useProgram(post);
    gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,texC);gl.uniform1i(UP.uC,0);
    gl.activeTexture(gl.TEXTURE1);gl.bindTexture(gl.TEXTURE_2D,texD);gl.uniform1i(UP.uD,1);
    gl.uniform1i(UP.uT,Math.max(1,Math.round(DPRc*0.9)));gl.uniform1f(UP.uThr,EDGE_THR/(2*zr));gl.uniform1f(UP.uFadeW,0.15*Math.min(cw,ch*0.75));
    gl.uniform3f(UP.uSil,OUT_SIL[0]/255,OUT_SIL[1]/255,OUT_SIL[2]/255);gl.uniform3f(UP.uInn,OUT_IN[0]/255,OUT_IN[1]/255,OUT_IN[2]/255);
    gl.bindVertexArray(vaoEmpty);gl.drawArrays(gl.TRIANGLES,0,3);
  }

  function frame(now){
    requestAnimationFrame(frame);
    if(!ready||!W)return;
    var dt=Math.min(0.1,(now-last)/1000);last=now;
    var req=api._req;want=(req&&fabs[req])?req:null;var moving=false;
    for(var k in fabs){var f=fabs[k],tg=(k===want)?1:0;
      if(f.t!==tg){f.t+=Math.sign(tg-f.t)*dt/0.75;if(Math.abs(f.t-tg)<0.02)f.t=tg;moving=true}
      f.e=f.t*f.t*(3-2*f.t)}
    if(want!==null&&hidKey!==want){hidKey=want;hidden=clashSet(want);uploadGlycans(hidden)}
    if(want===null&&hidKey!=='~'){hidKey='~';hidden={};uploadGlycans(hidden)}
    /* the structure turns only with the reader's scroll, eased so it glides to a stop */
    var target=window.EnvYaw?window.EnvYaw(dt):window.scrollY*0.0016;
    if(yawCur===null)yawCur=target;
    if(target!==yawCur)dirty=true;
    var diff=target-yawCur,spinning=Math.abs(diff)>0.0004;
    if(spinning)yawCur+=diff*Math.min(1,dt*6);else yawCur=target;
    var inMotion=spinning||moving;
    if(!inMotion&&!dirty&&!wasMoving)return;
    wasMoving=inMotion;dirty=false;
    render();
  }

  try{
    gl=cv.getContext('webgl2',{alpha:true,premultipliedAlpha:true,antialias:false,depth:false,stencil:false,preserveDrawingBuffer:false});
    if(!gl)throw new Error('context');
    prog=program(VS,FS);post=program(PVS,PFS);
    U=locs(prog,['uRot','uOff','uScale','uVP','uZR','uCue','uLight','uFlag']);
    U.uPal=gl.getUniformLocation(prog,'uPal');
    UP=locs(post,['uC','uD','uT','uThr','uFadeW','uSil','uInn']);
    gl.useProgram(prog);
    var pal=new Float32Array(21);for(var pi=0;pi<7;pi++){pal[pi*3]=PAL[pi][0]/255;pal[pi*3+1]=PAL[pi][1]/255;pal[pi*3+2]=PAL[pi][2]/255}
    gl.uniform3fv(U.uPal,pal);
    fbo=gl.createFramebuffer();vaoEmpty=gl.createVertexArray();
    size();
  }catch(e){fallback(e.message);return}

  api.info=function(){return {renderer:'webgl2',ext:ext,glycanPoints:gly&&gly.set.n,fabs:Object.keys(fabs)}};
  if(window.ResizeObserver)new ResizeObserver(size).observe(fig);else addEventListener('resize',size);
  load().then(function(){size();fig.classList.add('ready');requestAnimationFrame(frame)}).catch(function(e){console.error(e);fallback(e.message)});
})();
