/* 5FYJ Env trimer that turns with scroll, with a bound Fab that changes with the page section.
   Software surface renderer: Env and Fab are drawn as continuous, banded-shaded surfaces (depth-buffered
   probe-expanded spheres with contour lines at depth edges); Man9 glycans are drawn as thin ball-and-stick branches.
   Public API: window.EnvViewer.setFab('pgt122' | 'vrc01' | 'o22' | null) */
(function(){
  var C=window.ENV5FYJ,fig=document.getElementById('envFig'),cv=document.getElementById('envCanvas');
  if(!C||!fig||!cv)return;
  var H=C.h,FH=C.fh,ctx=cv.getContext('2d');
  var VDW=[1.7,1.55,1.52,1.8];
  var PROBE=0.13,BALL=0.10,STICK=0.07,EDGE_THR=0.30;                 /* nm */
  /* faded palette: class 1-3 protomers, 4 glycan, 5-6 Fab chains */
  var PAL=[null,[232,229,223],[226,223,217],[220,217,211],[238,168,148],[164,204,220],[190,200,234]];
  var OUT_SIL=[84,142,134],OUT_IN=[70,76,138];
  var LX=-0.42,LY=0.52,LZ=0.74;{var ll=Math.hypot(LX,LY,LZ);LX/=ll;LY/=ll;LZ/=ll}
  var BANDS=5,DEPTHS=4;
  var QUAL=[{bs:0.65,sd:2},{bs:0.5,sd:3},{bs:0.38,sd:4}];              /* reduced detail only while moving */
  var D=null,G=null,fabs={},want=null,req=(window.EnvViewer&&window.EnvViewer._req)||null,hidden={},hidKey='~',q=1,ema=14,lastAdj=0,W=0,Hh=0,DPRc=1.5,scale=1,ready=false;
  var pitch=0.28,yawCur=null,dirty=true,wasMoving=false,last=performance.now();
  var Z,Cl,Ls,off=document.createElement('canvas'),offCtx=off.getContext('2d'),img=null,u32=null,imgKey='';
  var LUT=[];

  /* colour look-up: [class][band][depth] -> packed ABGR */
  (function(){for(var c=1;c<PAL.length;c++){var row=[];for(var b=0;b<BANDS;b++){for(var d=0;d<DEPTHS;d++){
    var f=(0.78+0.22*b/(BANDS-1))*(0.90+0.10*d/(DEPTHS-1)),p=PAL[c];
    row.push((255<<24)|(Math.round(p[2]*f)<<16)|(Math.round(p[1]*f)<<8)|Math.round(p[0]*f))}}LUT[c]=row}})();
  var SIL=(255<<24)|(OUT_SIL[2]<<16)|(OUT_SIL[1]<<8)|OUT_SIL[0],INN=(255<<24)|(OUT_IN[2]<<16)|(OUT_IN[1]<<8)|OUT_IN[0];

  function b64(b){var s=atob(b),a=new Uint8Array(s.length);for(var i=0;i<s.length;i++)a[i]=s.charCodeAt(i);return a}
  async function inflate(b){var st=new Blob([b64(b)]).stream().pipeThrough(new DecompressionStream('gzip'));return await new Response(st).arrayBuffer()}

  async function load(){
    var buf=await inflate(C.d1),o=0;
    var i16=function(n){var a=new Int16Array(buf,o,n*3);o+=n*6;return a};
    var P=i16(H.nP),Gl=i16(H.nG);i16(H.nPB);i16(H.nGB);
    var u8=function(n){var a=new Uint8Array(buf,o,n);o+=n;return a};
    var Pe=u8(H.nP),Pp=u8(H.nP),Ge=u8(H.nG);u8(H.nPB);var Gt=u8(H.nG);u8(H.nP);var Gs=u8(H.nG);
    var b2=await inflate(C.d2),o2=0;
    var zmin=1e9,zmax=-1e9,rmax=0,gr=0,i;
    for(i=0;i<H.nP;i++){var z=P[i*3+2]/100;if(z<zmin)zmin=z;if(z>zmax)zmax=z;var r=Math.hypot(P[i*3]/100,P[i*3+1]/100);if(r>rmax)rmax=r}
    for(i=0;i<H.nG;i++){var g=Math.hypot(Gl[i*3]/100,Gl[i*3+1]/100);if(g>gr)gr=g}
    var height=zmax-zmin,zc=height/2,gw=2*gr;
    var px=new Float32Array(H.nP),py=new Float32Array(H.nP),pz=new Float32Array(H.nP),pr=new Float32Array(H.nP),pc=new Uint8Array(H.nP);
    for(i=0;i<H.nP;i++){px[i]=-P[i*3]/100;py[i]=P[i*3+1]/100;pz[i]=P[i*3+2]/100-zmin-zc;pr[i]=VDW[Pe[i]]/10;pc[i]=Pp[i]+1}
    var gx=new Float32Array(H.nG),gy=new Float32Array(H.nG),gz=new Float32Array(H.nG);
    for(i=0;i<H.nG;i++){gx[i]=-Gl[i*3]/100;gy[i]=Gl[i*3+1]/100;gz[i]=Gl[i*3+2]/100-zmin-zc}
    /* glycan covalent bonds (heavy-atom distance < 1.9 A), found once with a grid */
    var cell=1.9,grid={},ba=[],bb=[],j,k,key;
    for(i=0;i<H.nG;i++){key=Math.floor(Gl[i*3]/10/cell)+','+Math.floor(Gl[i*3+1]/10/cell)+','+Math.floor(Gl[i*3+2]/10/cell);(grid[key]||(grid[key]=[])).push(i)}
    for(i=0;i<H.nG;i++){
      var ax=Gl[i*3]/10,ay=Gl[i*3+1]/10,az=Gl[i*3+2]/10,ix=Math.floor(ax/cell),iy=Math.floor(ay/cell),iz=Math.floor(az/cell);
      for(var a=-1;a<2;a++)for(var b=-1;b<2;b++)for(var c=-1;c<2;c++){
        var L=grid[(ix+a)+','+(iy+b)+','+(iz+c)];if(!L)continue;
        for(k=0;k<L.length;k++){j=L[k];if(j<=i)continue;
          var dx=Gl[j*3]/10-ax,dy=Gl[j*3+1]/10-ay,dz=Gl[j*3+2]/10-az;
          if(dx*dx+dy*dy+dz*dz<3.61){ba.push(i);bb.push(j)}}}}
    D={px:px,py:py,pz:pz,pr:pr,pc:pc,gx:gx,gy:gy,gz:gz,Gs:Gs,Graw:Gl,ba:Int32Array.from(ba),bb:Int32Array.from(bb),height:height,gw:gw};
    var ext=Math.max(height+2,gw)*1.05;
    FH.forEach(function(h){
      var P2=new Int16Array(b2,o2,h.n*3);o2+=h.n*6;var e=new Uint8Array(b2,o2,h.n);o2+=h.n;var c=new Uint8Array(b2,o2,h.n);o2+=h.n;
      var x=new Float32Array(h.n),y=new Float32Array(h.n),zz=new Float32Array(h.n),r=new Float32Array(h.n),cl=new Uint8Array(h.n),cx=0,cy=0,rb=0,j2;
      for(j2=0;j2<h.n;j2++){var rx=P2[j2*3]/100,ry=P2[j2*3+1]/100;x[j2]=-rx;y[j2]=ry;zz[j2]=P2[j2*3+2]/100-zmin-zc;r[j2]=VDW[e[j2]]/10;cl[j2]=c[j2]?6:5;cx+=x[j2];cy+=y[j2]}
      cx/=h.n;cy/=h.n;
      for(j2=0;j2<h.n;j2++)rb=Math.max(rb,Math.sqrt(x[j2]*x[j2]+y[j2]*y[j2]+zz[j2]*zz[j2]));
      ext=Math.max(ext,2*Math.max(rb+0.2,Math.hypot(gw/2,height/2))*1.04);
      fabs[h.k]={n:h.n,x:x,y:y,z:zz,r:r,c:cl,raw:P2,phi:Math.atan2(cy,cx),t:0,e:0,rb:rb};
    });
    var cap=0;for(var fk in fabs)cap=Math.max(cap,fabs[fk].n);
    G={ext:ext,SX:new Float32Array(H.nP+cap),SY:new Float32Array(H.nP+cap),SD:new Float32Array(H.nP+cap),
       GX:new Float32Array(H.nG),GY:new Float32Array(H.nG),GD:new Float32Array(H.nG)};
    ready=true;
  }

  /* glycans that sit where the Fab binds are hidden, as in the report */
  function clashSet(key){
    var set={};if(!key)return set;
    var F=fabs[key],Cc=2.8,grid={},j,k;
    for(j=0;j<F.n;j++){var x=F.raw[j*3]/10,y=F.raw[j*3+1]/10,z=F.raw[j*3+2]/10,kk=Math.floor(x/Cc)+','+Math.floor(y/Cc)+','+Math.floor(z/Cc);(grid[kk]||(grid[kk]=[])).push([x,y,z])}
    for(k=0;k<H.nG;k++){
      var X=D.Graw[k*3]/10,Y=D.Graw[k*3+1]/10,Zz=D.Graw[k*3+2]/10,ix=Math.floor(X/Cc),iy=Math.floor(Y/Cc),iz=Math.floor(Zz/Cc),hit=false;
      if(set[D.Gs[k]])continue;
      for(var a=-1;a<2&&!hit;a++)for(var b=-1;b<2&&!hit;b++)for(var c=-1;c<2&&!hit;c++){
        var L=grid[(ix+a)+','+(iy+b)+','+(iz+c)];if(!L)continue;
        for(var qq=0;qq<L.length;qq++){var dx=L[qq][0]-X,dy=L[qq][1]-Y,dz=L[qq][2]-Zz;if(dx*dx+dy*dy+dz*dz<Cc*Cc){hit=true;break}}}
      if(hit)set[D.Gs[k]]=1}
    return set;
  }

  function size(){
    var r=fig.getBoundingClientRect();W=Math.max(1,Math.round(r.width));Hh=Math.max(1,Math.round(r.height));
    DPRc=Math.max(1.5,Math.min(window.devicePixelRatio||1,2));
    cv.width=Math.round(W*DPRc);cv.height=Math.round(Hh*DPRc);
    var n=cv.width*cv.height;Z=new Float32Array(n);Cl=new Uint8Array(n);Ls=new Uint8Array(n);
    if(G)scale=Math.min(W,Hh)/G.ext*1.05;
    dirty=true;
  }

  /* ---- rasteriser state for one frame ---- */
  var bw=0,bh=0;
  function sphere(px,py,rpx,zc,rnm,cls){
    var x0=Math.max(0,Math.floor(px-rpx)),x1=Math.min(bw-1,Math.ceil(px+rpx)),y0=Math.max(0,Math.floor(py-rpx)),y1=Math.min(bh-1,Math.ceil(py+rpx));
    var r2=rpx*rpx,inv=1/rpx,inv2=1/r2,x,y,dx,dy,d2,nz,zz,idx,L;
    for(y=y0;y<=y1;y++){dy=y+0.5-py;for(x=x0;x<=x1;x++){dx=x+0.5-px;d2=dx*dx+dy*dy;if(d2>r2)continue;
      nz=Math.sqrt(1-d2*inv2);zz=zc+nz*rnm;idx=y*bw+x;
      if(zz>Z[idx]){Z[idx]=zz;Cl[idx]=cls;L=dx*inv*LX-dy*inv*LY+nz*LZ;Ls[idx]=L>0?(L*255)|0:0}}}
  }

  function frame(now){
    requestAnimationFrame(frame);
    if(!ready||!W)return;
    var dt=Math.min(0.1,(now-last)/1000);last=now;
    /* Fab slide in / out */
    want=(req&&fabs[req])?req:null;var moving=false;
    for(var k in fabs){var f=fabs[k],tg=(k===want)?1:0;
      if(f.t!==tg){f.t+=Math.sign(tg-f.t)*dt/0.75;if(Math.abs(f.t-tg)<0.02||(tg>f.t&&f.t>tg)||(tg<f.t&&f.t<tg))f.t=tg;moving=true}
      f.e=f.t*f.t*(3-2*f.t)}
    if(want!==null&&hidKey!==want){hidKey=want;hidden=clashSet(want)}
    if(want===null&&hidKey!=='~'){hidKey='~';hidden={}}
    /* the structure turns only with the reader's scroll, eased so it glides to a stop */
    var target=window.scrollY*0.0016;
    if(yawCur===null)yawCur=target;
    var diff=target-yawCur,spinning=Math.abs(diff)>0.0004;
    if(spinning)yawCur+=diff*Math.min(1,dt*6);else yawCur=target;
    var inMotion=spinning||moving;
    if(wasMoving&&!inMotion)dirty=true;                 /* one last full-detail frame when it settles */
    wasMoving=inMotion;
    if(!inMotion&&!dirty)return;
    dirty=false;
    render(inMotion,now,moving,null);
  }

  function render(inMotion,now,moving,forceQ){
    var t0=performance.now();
    var Qc=forceQ||(inMotion?QUAL[q]:{bs:1,sd:1}),sd=Qc.sd;
    bw=Math.max(8,Math.round(cv.width*Qc.bs));bh=Math.max(8,Math.round(cv.height*Qc.bs));
    var npx=bw*bh;Z.fill(-1e9,0,npx);Cl.fill(0,0,npx);
    var sP=scale*DPRc*Qc.bs,cx=bw*0.5,cy=bh*0.5;
    var cyw=Math.cos(yawCur),syw=Math.sin(yawCur),cp=Math.cos(pitch),sp=Math.sin(pitch);
    var SX=G.SX,SY=G.SY,SD=G.SD,i,x,y,z,xs,d0,n=0,dmin=1e9,dmax=-1e9;
    /* protein */
    for(i=0;i<H.nP;i+=sd){x=D.px[i];y=D.py[i];z=D.pz[i];xs=x*cyw-y*syw;d0=x*syw+y*cyw;
      SX[n]=xs;SY[n]=z*cp-d0*sp;var dd=z*sp+d0*cp;SD[n]=dd;if(dd<dmin)dmin=dd;if(dd>dmax)dmax=dd;n++}
    var span=(dmax-dmin)||1;
    var nProt=n,rExtra=(sd-1)*0.03;
    for(i=0,n=0;i<H.nP;i+=sd,n++){var rn=D.pr[i]+PROBE+rExtra;sphere(cx+sP*SX[n],cy-sP*SY[n],sP*rn,SD[n],rn,D.pc[i])}
    /* Fab surface */
    for(var fk in fabs){var F=fabs[fk];if(F.e<0.01)continue;
      var off0=(1-F.e)*7,ox=Math.cos(F.phi)*off0,oy=Math.sin(F.phi)*off0;
      for(i=0;i<F.n;i+=sd){x=F.x[i]+ox;y=F.y[i]+oy;z=F.z[i];xs=x*cyw-y*syw;d0=x*syw+y*cyw;
        var rn2=F.r[i]+PROBE+rExtra;sphere(cx+sP*xs,cy-sP*(z*cp-d0*sp),sP*rn2,z*sp+d0*cp,rn2,F.c[i])}}
    /* glycans: ball and stick, depth-tested against the surfaces */
    var GX=G.GX,GY=G.GY,GD=G.GD;
    for(i=0;i<H.nG;i++){x=D.gx[i];y=D.gy[i];z=D.gz[i];xs=x*cyw-y*syw;d0=x*syw+y*cyw;GX[i]=cx+sP*xs;GY[i]=cy-sP*(z*cp-d0*sp);GD[i]=z*sp+d0*cp}
    var stickPx=Math.max(1.1,sP*STICK),ballPx=Math.max(1.5,sP*BALL);
    if(sd===1){
      for(i=0;i<H.nG;i++){if(hidden[D.Gs[i]])continue;sphere(GX[i],GY[i],ballPx,GD[i],BALL,4)}
      for(var bi=0;bi<D.ba.length;bi++){var a=D.ba[bi],b=D.bb[bi];if(hidden[D.Gs[a]])continue;
        var x1=GX[a],y1=GY[a],x2=GX[b],y2=GY[b],len=Math.hypot(x2-x1,y2-y1),steps=Math.max(1,Math.ceil(len/(stickPx*0.7)));
        for(var st=1;st<steps;st++){var tt=st/steps;sphere(x1+(x2-x1)*tt,y1+(y2-y1)*tt,stickPx,GD[a]+(GD[b]-GD[a])*tt,STICK,4)}}
    }else{                                   /* while moving: one blob per bond, no balls */
      var mr=Math.max(1.2,sP*0.1);
      for(var bj=0;bj<D.ba.length;bj+=sd>2?2:1){var a2=D.ba[bj],b2i=D.bb[bj];if(hidden[D.Gs[a2]])continue;
        sphere((GX[a2]+GX[b2i])*0.5,(GY[a2]+GY[b2i])*0.5,mr,(GD[a2]+GD[b2i])*0.5,BALL,4)}
    }
    /* compose: banded shading + contour lines at silhouettes and depth edges */
    var key=bw+'x'+bh;
    if(imgKey!==key){off.width=bw;off.height=bh;img=offCtx.createImageData(bw,bh);u32=new Uint32Array(img.data.buffer);imgKey=key}
    var T=Math.max(1,Math.round(DPRc*Qc.bs*0.9)),idx,c,zc0,lv,dl,nb,edge,row,xx,yy;
    for(yy=0;yy<bh;yy++){row=yy*bw;for(xx=0;xx<bw;xx++){idx=row+xx;c=Cl[idx];
      if(!c){u32[idx]=0;continue}
      zc0=Z[idx];edge=0;
      if(c===4){lv=Math.min(BANDS-1,(Ls[idx]*BANDS/256)|0);dl=Math.max(0,Math.min(DEPTHS-1,(((zc0-dmin)/span)*DEPTHS)|0));u32[idx]=LUT[4][lv*DEPTHS+dl];continue}   /* glycan sticks: shading only, no contour */
      if(xx<T||xx>=bw-T||yy<T||yy>=bh-T){edge=1}
      else{
        nb=idx-T;if(!Cl[nb])edge=1;else if(Z[nb]-zc0>EDGE_THR)edge=edge||2;
        nb=idx+T;if(!Cl[nb])edge=1;else if(Z[nb]-zc0>EDGE_THR)edge=edge||2;
        nb=idx-T*bw;if(!Cl[nb])edge=1;else if(Z[nb]-zc0>EDGE_THR)edge=edge||2;
        nb=idx+T*bw;if(!Cl[nb])edge=1;else if(Z[nb]-zc0>EDGE_THR)edge=edge||2}
      if(edge){u32[idx]=edge===1?SIL:INN;continue}
      lv=Math.min(BANDS-1,(Ls[idx]*BANDS/256)|0);
      dl=Math.max(0,Math.min(DEPTHS-1,(((zc0-dmin)/span)*DEPTHS)|0));
      u32[idx]=LUT[c][lv*DEPTHS+dl]}}
    /* soft fade toward the panel edges instead of a hard crop */
    var zone=Math.max(2,Math.round(0.15*Math.min(bw,bh*0.75))),fxx,fa,col;
    for(yy=0;yy<bh;yy++){row=yy*bw;
      var fyy=Math.min(yy,bh-1-yy)/zone;fyy=fyy>=1?1:fyy*fyy*(3-2*fyy);
      for(xx=0;xx<bw;xx++){
        if(xx>=zone&&xx<bw-zone){if(fyy>=1){xx=bw-zone-1;continue}}
        fxx=Math.min(xx,bw-1-xx)/zone;fxx=fxx>=1?1:fxx*fxx*(3-2*fxx);fa=fxx*fyy;
        if(fa<1){col=u32[row+xx];if(col){u32[row+xx]=((Math.round(255*fa)<<24)|(col&0xFFFFFF))>>>0}}}}
    offCtx.putImageData(img,0,0);
    ctx.clearRect(0,0,cv.width,cv.height);ctx.imageSmoothingEnabled=true;ctx.imageSmoothingQuality='high';
    ctx.drawImage(off,0,0,bw,bh,0,0,cv.width,cv.height);
    /* adaptive quality while moving */
    if(forceQ)return performance.now()-t0;
    if(inMotion){var ms=performance.now()-t0;ema=ema*0.85+ms*0.15;
      if(now-lastAdj>900){if(ema>26&&q<QUAL.length-1){q++;lastAdj=now}else if(ema<9&&q>0&&!moving){q--;lastAdj=now}}}
  }

  window.EnvViewer={bench:function(l){if(!ready)return null;var Qs=l<0?{bs:1,sd:1}:QUAL[l];render(l>=0,performance.now(),false,Qs);var s=0;for(var i=0;i<5;i++)s+=render(l>=0,performance.now(),false,Qs);return Math.round(s/5*10)/10},setFab:function(k){req=k||null},info:function(){var o={ext:G&&G.ext,gw:D&&D.gw,h:D&&D.height,bonds:D&&D.ba.length,q:q,ema:Math.round(ema),fabs:{}};for(var k in fabs)o.fabs[k]=fabs[k].rb;return o}};
  size();
  if(window.ResizeObserver)new ResizeObserver(size).observe(fig);else addEventListener('resize',size);
  if(!window.DecompressionStream){fig.classList.add('unsupported');return}
  load().then(function(){size();fig.classList.add('ready');requestAnimationFrame(frame)}).catch(function(e){fig.classList.add('unsupported');console.error(e)});
})();
