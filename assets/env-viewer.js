/* 5FYJ Env trimer that turns with scroll, with a bound Fab that changes with the page section.
   Canvas-2D painter's-algorithm renderer (same look as the Virion Portrait companion).
   Public API: window.EnvViewer.setFab('pgt122' | 'vrc01' | 'o22' | null) */
(function(){
  var C=window.ENV5FYJ,fig=document.getElementById('envFig'),cv=document.getElementById('envCanvas');
  if(!C||!fig||!cv)return;
  var H=C.h,FH=C.fh,ctx=cv.getContext('2d');
  var INK='#10201C',VDW=[1.7,1.55,1.52,1.8];
  var PROT=[[46,143,131],[63,168,154],[38,120,110]],GLY=[227,154,85],ABC=[[104,122,188],[126,142,206]];
  var BASE=[PROT[0],PROT[1],PROT[2],GLY,ABC[0],ABC[1]];           /* colour classes */
  var COL=BASE.map(function(c){var a=[];for(var l=0;l<=32;l++){var f=l/32;a.push('rgb('+Math.round(c[0]*f)+','+Math.round(c[1]*f)+','+Math.round(c[2]*f)+')')}return a});
  var reduce=window.matchMedia&&matchMedia('(prefers-reduced-motion: reduce)').matches;
  var D=null,G=null,fabs={},want=null,hidden={},hidKey='~',stp=2,ema=12,lastAdj=0,W=0,Hh=0,DPR=1,scale=1,ready=false;
  var pitch=0.28;

  function b64(b){var s=atob(b),a=new Uint8Array(s.length);for(var i=0;i<s.length;i++)a[i]=s.charCodeAt(i);return a}
  async function inflate(b){var st=new Blob([b64(b)]).stream().pipeThrough(new DecompressionStream('gzip'));return await new Response(st).arrayBuffer()}

  async function load(){
    var buf=await inflate(C.d1),o=0;
    var i16=function(n){var a=new Int16Array(buf,o,n*3);o+=n*6;return a};
    var P=i16(H.nP),Gl=i16(H.nG);i16(H.nPB);i16(H.nGB);
    var u8=function(n){var a=new Uint8Array(buf,o,n);o+=n;return a};
    var Pe=u8(H.nP),Pp=u8(H.nP),Ge=u8(H.nG);u8(H.nPB);var Gt=u8(H.nG);u8(H.nP);var Gs=u8(H.nG);
    var b2=await inflate(C.d2),o2=0;
    /* geometry: nm, z up, centred on the trimer */
    var zmin=1e9,zmax=-1e9,rmax=0,gr=0,i;
    for(i=0;i<H.nP;i++){var z=P[i*3+2]/100;if(z<zmin)zmin=z;if(z>zmax)zmax=z;var r=Math.hypot(P[i*3]/100,P[i*3+1]/100);if(r>rmax)rmax=r}
    for(i=0;i<H.nG;i++){var g=Math.hypot(Gl[i*3]/100,Gl[i*3+1]/100);if(g>gr)gr=g}
    var height=zmax-zmin,zc=height/2,gw=2*gr;
    var px=new Float32Array(H.nP),py=new Float32Array(H.nP),pz=new Float32Array(H.nP),pr=new Float32Array(H.nP),pc=new Uint8Array(H.nP);
    for(i=0;i<H.nP;i++){px[i]=-P[i*3]/100;py[i]=P[i*3+1]/100;pz[i]=P[i*3+2]/100-zmin-zc;pr[i]=VDW[Pe[i]]/10;pc[i]=Pp[i]}
    var gx=new Float32Array(H.nG),gy=new Float32Array(H.nG),gz=new Float32Array(H.nG),gr2=new Float32Array(H.nG);
    for(i=0;i<H.nG;i++){gx[i]=-Gl[i*3]/100;gy[i]=Gl[i*3+1]/100;gz[i]=Gl[i*3+2]/100-zmin-zc;gr2[i]=VDW[Ge[i]]/10*0.86}
    D={px:px,py:py,pz:pz,pr:pr,pc:pc,gx:gx,gy:gy,gz:gz,gr:gr2,Gs:Gs,Graw:Gl,height:height,gw:gw};
    var ext=Math.max(height+2,gw)*1.05;
    FH.forEach(function(h){
      var P2=new Int16Array(b2,o2,h.n*3);o2+=h.n*6;var e=new Uint8Array(b2,o2,h.n);o2+=h.n;var c=new Uint8Array(b2,o2,h.n);o2+=h.n;
      var x=new Float32Array(h.n),y=new Float32Array(h.n),zz=new Float32Array(h.n),r=new Float32Array(h.n),cl=new Uint8Array(h.n),cx=0,cy=0,rb=0,j;
      for(j=0;j<h.n;j++){var rx=P2[j*3]/100,ry=P2[j*3+1]/100;x[j]=-rx;y[j]=ry;zz[j]=P2[j*3+2]/100-zmin-zc;r[j]=VDW[e[j]]/10;cl[j]=c[j]?5:4;cx+=x[j];cy+=y[j]}
      cx/=h.n;cy/=h.n;
      for(j=0;j<h.n;j++)rb=Math.max(rb,Math.sqrt(x[j]*x[j]+y[j]*y[j]+zz[j]*zz[j]));
      ext=Math.max(ext,2*Math.max(rb+0.2,Math.hypot(gw/2,height/2))*1.04);
      fabs[h.k]={n:h.n,x:x,y:y,z:zz,r:r,c:cl,raw:P2,phi:Math.atan2(cy,cx),t:0,target:0};
    });
    G={ext:ext};
    var cap=0;for(var k in fabs)cap=Math.max(cap,fabs[k].n);
    var tot=H.nP+H.nG+cap;
    G.X=new Float32Array(tot);G.Y=new Float32Array(tot);G.Dp=new Float32Array(tot);G.R=new Float32Array(tot);G.Cb=new Uint8Array(tot);G.order=[];
    ready=true;
  }

  /* glycans that sit where the Fab binds are hidden, as in the report */
  function clashSet(key){
    var set={};if(!key)return set;
    var F=fabs[key],Cc=2.8,grid={},j,k;
    for(j=0;j<F.n;j++){var x=F.raw[j*3]/10,y=F.raw[j*3+1]/10,z=F.raw[j*3+2]/10,kk=Math.floor(x/Cc)+','+Math.floor(y/Cc)+','+Math.floor(z/Cc);(grid[kk]||(grid[kk]=[])).push([x,y,z])}
    for(k=0;k<H.nG;k++){
      var X=D.Graw[k*3]/10,Y=D.Graw[k*3+1]/10,Z=D.Graw[k*3+2]/10,ix=Math.floor(X/Cc),iy=Math.floor(Y/Cc),iz=Math.floor(Z/Cc),hit=false;
      if(set[D.Gs[k]])continue;
      for(var a=-1;a<2&&!hit;a++)for(var b=-1;b<2&&!hit;b++)for(var c=-1;c<2&&!hit;c++){
        var L=grid[(ix+a)+','+(iy+b)+','+(iz+c)];if(!L)continue;
        for(var q=0;q<L.length;q++){var dx=L[q][0]-X,dy=L[q][1]-Y,dz=L[q][2]-Z;if(dx*dx+dy*dy+dz*dz<Cc*Cc){hit=true;break}}}
      if(hit)set[D.Gs[k]]=1}
    return set;
  }

  function size(){
    var r=fig.getBoundingClientRect();W=Math.max(1,Math.round(r.width));Hh=Math.max(1,Math.round(r.height));
    DPR=Math.min(window.devicePixelRatio||1,1.75);
    dirty=true;
    cv.width=Math.round(W*DPR);cv.height=Math.round(Hh*DPR);
    if(G)scale=Math.min(W,Hh)/G.ext*1.18;
  }

  var yaw0=0,yawCur=null,dirty=true,last=performance.now();
  function frame(now){
    requestAnimationFrame(frame);
    if(!ready||!W)return;
    var dt=Math.min(0.1,(now-last)/1000);last=now;
    /* Fab slide in / out */
    want=(req&&fabs[req])?req:null;var moving=false;
    for(var k in fabs){var f=fabs[k],tg=(k===want)?1:0;
      if(f.t!==tg){f.t+=Math.sign(tg-f.t)*dt/0.75;if((tg>f.t&&f.t>tg-0.001)||(tg<f.t&&f.t<tg+0.001)||Math.abs(f.t-tg)<0.02)f.t=tg;moving=true}
      f.e=f.t*f.t*(3-2*f.t)}
    if(want!==null&&hidKey!==want){hidKey=want;hidden=clashSet(want)}
    if(want===null&&hidKey!=='~'){hidKey='~';hidden={}}
    /* the structure turns only with the reader's scroll, eased so it glides to a stop */
    var target=yaw0+window.scrollY*0.0016;
    if(yawCur===null)yawCur=target;
    var diff=target-yawCur,spinning=Math.abs(diff)>0.0004;
    if(spinning)yawCur+=diff*Math.min(1,dt*6);else yawCur=target;
    if(!spinning&&!moving&&!dirty)return;
    dirty=false;
    var yaw=yawCur;
    var cyw=Math.cos(yaw),syw=Math.sin(yaw),cp=Math.cos(pitch),sp=Math.sin(pitch);
    var X=G.X,Y=G.Y,Dp=G.Dp,R=G.R,Cb=G.Cb,n=0,dmin=1e9,dmax=-1e9,i,x,y,z,xs,d0,lm=1+0.22*(stp-1);
    for(i=0;i<H.nP;i+=stp){x=D.px[i];y=D.py[i];z=D.pz[i];xs=x*cyw-y*syw;d0=x*syw+y*cyw;
      X[n]=xs;Y[n]=z*cp-d0*sp;Dp[n]=z*sp+d0*cp;R[n]=D.pr[i]*lm;Cb[n]=D.pc[i];n++}
    for(i=0;i<H.nG;i+=stp){if(hidden[D.Gs[i]])continue;x=D.gx[i];y=D.gy[i];z=D.gz[i];xs=x*cyw-y*syw;d0=x*syw+y*cyw;
      X[n]=xs;Y[n]=z*cp-d0*sp;Dp[n]=z*sp+d0*cp;R[n]=D.gr[i]*lm;Cb[n]=3;n++}
    for(var fk in fabs){var F=fabs[fk];if(F.e<0.01)continue;
      var off=(1-F.e)*7,ox=Math.cos(F.phi)*off,oy=Math.sin(F.phi)*off;
      for(i=0;i<F.n;i+=stp){x=F.x[i]+ox;y=F.y[i]+oy;z=F.z[i];xs=x*cyw-y*syw;d0=x*syw+y*cyw;
        X[n]=xs;Y[n]=z*cp-d0*sp;Dp[n]=z*sp+d0*cp;R[n]=F.r[i]*lm;Cb[n]=F.c[i];n++}}
    for(i=0;i<n;i++){if(Dp[i]<dmin)dmin=Dp[i];if(Dp[i]>dmax)dmax=Dp[i]}
    var ord=G.order;ord.length=n;for(i=0;i<n;i++)ord[i]=i;
    ord.sort(function(a,b){return Dp[a]-Dp[b]});
    ctx.setTransform(DPR,0,0,DPR,0,0);ctx.clearRect(0,0,W,Hh);
    var cx=W*0.5,cy=Hh*0.5,s=scale,span=(dmax-dmin)||1,ow=Math.max(1.2,s*0.1),j,it;
    ctx.fillStyle=INK;
    for(j=0;j<n;j++){it=ord[j];ctx.beginPath();ctx.arc(cx+s*X[it],cy-s*Y[it],s*R[it]+ow,0,6.2832);ctx.fill()}
    for(j=0;j<n;j++){it=ord[j];var lv=Math.round((0.7+0.3*(Dp[it]-dmin)/span)*32);
      ctx.beginPath();ctx.arc(cx+s*X[it],cy-s*Y[it],s*R[it],0,6.2832);ctx.fillStyle=COL[Cb[it]][lv];ctx.fill()}
    /* adaptive quality: keep the spin smooth on slower machines */
    var ms=performance.now()-now;ema=ema*0.9+ms*0.1;
    if(now-lastAdj>1200){if(ema>20&&stp<4){stp++;lastAdj=now}else if(ema<7&&stp>1&&!moving){stp--;lastAdj=now}}
  }

  var req=null;window.EnvViewer={setFab:function(k){req=k||null}};
  size();
  if(window.ResizeObserver)new ResizeObserver(size).observe(fig);else addEventListener('resize',size);
  if(!window.DecompressionStream){fig.classList.add('unsupported');return}
  load().then(function(){size();fig.classList.add('ready');requestAnimationFrame(frame)}).catch(function(e){fig.classList.add('unsupported');console.error(e)});
})();
