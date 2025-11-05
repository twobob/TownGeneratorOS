// Minimal pure-JS 3D math + Camera + projection utilities
// Lightweight, zero-dependency module intended to plug into the existing Canvas renderer.

// Vec3 simple helper
class Vec3 {
  constructor(x=0,y=0,z=0){ this.x=x; this.y=y; this.z=z; }
  clone(){ return new Vec3(this.x,this.y,this.z); }
  sub(b){ return new Vec3(this.x-b.x, this.y-b.y, this.z-b.z); }
  add(b){ return new Vec3(this.x+b.x, this.y+b.y, this.z+b.z); }
  mulScalar(s){ return new Vec3(this.x*s,this.y*s,this.z*s); }
  length(){ return Math.sqrt(this.x*this.x+this.y*this.y+this.z*this.z); }
  normalize(){ const l=this.length()||1; this.x/=l; this.y/=l; this.z/=l; return this; }
  static cross(a,b){ return new Vec3(a.y*b.z-a.z*b.y, a.z*b.x-a.x*b.z, a.x*b.y-a.y*b.x); }
  static dot(a,b){ return a.x*b.x + a.y*b.y + a.z*b.z; }
}

// Mat4 column-major storage (Float32Array[16])
class Mat4 {
  constructor(){ this.m = new Float32Array(16); Mat4.identityTo(this.m); }
  static identityTo(out){
    out[0]=1; out[1]=0; out[2]=0; out[3]=0;
    out[4]=0; out[5]=1; out[6]=0; out[7]=0;
    out[8]=0; out[9]=0; out[10]=1; out[11]=0;
    out[12]=0; out[13]=0; out[14]=0; out[15]=1;
  }
  static multiply(a,b,out){
    // out = a * b
    const am=a, bm=b, o=out;
    for(let i=0;i<4;i++){
      const ai0=am[i], ai1=am[i+4], ai2=am[i+8], ai3=am[i+12];
      o[i]   = ai0*bm[0]  + ai1*bm[1]  + ai2*bm[2]  + ai3*bm[3];
      o[i+4] = ai0*bm[4]  + ai1*bm[5]  + ai2*bm[6]  + ai3*bm[7];
      o[i+8] = ai0*bm[8]  + ai1*bm[9]  + ai2*bm[10] + ai3*bm[11];
      o[i+12]= ai0*bm[12] + ai1*bm[13] + ai2*bm[14] + ai3*bm[15];
    }
  }
  static lookAt(eye, target, up, out){
    // compute right-handed lookAt (camera points toward -Z in view space)
    const z = new Vec3(eye.x-target.x, eye.y-target.y, eye.z-target.z).normalize();
    const x = Vec3.cross(up, z).normalize();
    const y = Vec3.cross(z, x).normalize();
    // column-major
    out[0]=x.x; out[1]=y.x; out[2]=z.x; out[3]=0;
    out[4]=x.y; out[5]=y.y; out[6]=z.y; out[7]=0;
    out[8]=x.z; out[9]=y.z; out[10]=z.z; out[11]=0;
    out[12]=-(x.x*eye.x + x.y*eye.y + x.z*eye.z);
    out[13]=-(y.x*eye.x + y.y*eye.y + y.z*eye.z);
    out[14]=-(z.x*eye.x + z.y*eye.y + z.z*eye.z);
    out[15]=1;
  }
  static perspective(fovDeg, aspect, near, far, out){
    const fovRad = fovDeg * Math.PI / 180;
    const f = 1.0 / Math.tan(fovRad/2);
    // column-major
    out[0]=f/aspect; out[1]=0; out[2]=0; out[3]=0;
    out[4]=0; out[5]=f; out[6]=0; out[7]=0;
    out[8]=0; out[9]=0; out[10]=(far+near)/(near-far); out[11]=-1;
    out[12]=0; out[13]=0; out[14]=(2*far*near)/(near-far); out[15]=0;
  }
}

class Camera {
  constructor(fov=60, aspect=1.0, near=0.1, far=4000){
    this.position = new Vec3(0,6,0); // default 6 units up
    this.target = new Vec3(0,0,1);
    this.up = new Vec3(0,1,0);
    this.fov = fov; this.aspect = aspect; this.near = near; this.far = far;
    this.viewMat = new Float32Array(16);
    this.projMat = new Float32Array(16);
    this.viewProj = new Float32Array(16);
    Mat4.lookAt(this.position,this.target,this.up,this.viewMat);
    Mat4.perspective(this.fov,this.aspect,this.near,this.far,this.projMat);
    Mat4.multiply(this.projMat,this.viewMat,this.viewProj);
  }
  setPerspective(fov, aspect, near, far){ this.fov=fov; this.aspect=aspect; this.near=near; this.far=far; Mat4.perspective(this.fov,this.aspect,this.near,this.far,this.projMat); Mat4.multiply(this.projMat,this.viewMat,this.viewProj); }
  lookAt(target){ this.target = target; Mat4.lookAt(this.position,this.target,this.up,this.viewMat); Mat4.multiply(this.projMat,this.viewMat,this.viewProj); }
  setPosition(pos){ this.position = pos; Mat4.lookAt(this.position,this.target,this.up,this.viewMat); Mat4.multiply(this.projMat,this.viewMat,this.viewProj); }
  // project a world-space Vec3 to screen coordinates (px,py) and normalized depth
  projectPoint(v, canvasWidth, canvasHeight){
    const m = this.viewProj;
    const vm = this.viewMat;
    // transform to view space first (for proper Z clipping)
    const x = v.x, y = v.y, z = v.z;
    const vx = vm[0]*x + vm[4]*y + vm[8]*z + vm[12];
    const vy = vm[1]*x + vm[5]*y + vm[9]*z + vm[13];
    const vz = vm[2]*x + vm[6]*y + vm[10]*z + vm[14];
    
    // transform to clip space
    const tx = m[0]*x + m[4]*y + m[8]*z + m[12];
    const ty = m[1]*x + m[5]*y + m[9]*z + m[13];
    const tz = m[2]*x + m[6]*y + m[10]*z + m[14];
    const tw = m[3]*x + m[7]*y + m[11]*z + m[15];
    if(Math.abs(tw) < 1e-6) return {visible:false, viewZ: vz};
    const ndcX = tx / tw; const ndcY = ty / tw; const ndcZ = tz / tw;
    const screenX = (ndcX * 0.5 + 0.5) * canvasWidth;
    const screenY = ( -ndcY * 0.5 + 0.5) * canvasHeight; // flip Y for canvas
    return { 
      x: screenX, 
      y: screenY, 
      depth: ndcZ, 
      viewZ: vz,  // View-space Z for proper clipping
      ndcX, 
      ndcY, 
      visible: (ndcZ >= -1 && ndcZ <= 1 && ndcX>=-1 && ndcX<=1 && ndcY>=-1 && ndcY<=1) 
    };
  }
}

// Lightweight mesh extrusion: top polygon (array of Vec3) to walls + top face
function extrudePolygonToMesh(polygon2D, height){
  // polygon2D: array of {x,y} in world 2D coords (mapped to X,Z in 3D)
  // returns { vertices: Vec3[], faces: [i0,i1,i2] triangles }
  const verts = [];
  // bottom vertices (y=0, on ground)
  for(const p of polygon2D) verts.push(new Vec3(p.x, 0, p.y));
  // top vertices (y=height)
  for(const p of polygon2D) verts.push(new Vec3(p.x, height, p.y));
  const n = polygon2D.length;
  const faces = [];
  // top fan (assume polygon is convex-ish; simple triangulation)
  for(let i=1;i<n-1;i++) faces.push([n,n+i,n+i+1]);
  // bottom fan (reverse order for correct winding)
  for(let i=1;i<n-1;i++) faces.push([0, i+1, i]);
  // walls
  for(let i=0;i<n;i++){
    const a = i;
    const b = (i+1)%n;
    const aBot = a;
    const bBot = b;
    const aTop = n + a;
    const bTop = n + b;
    // two triangles per quad wall
    faces.push([aBot, bBot, aTop]);
    faces.push([bBot, bTop, aTop]);
  }
  return { vertices: verts, faces };
}

// Simple painter: project each triangle, compute average depth, sort, draw with shading and shadows
function drawMesh(ctx, mesh, camera, canvasWidth, canvasHeight, style, castShadows){
  const projected = [];
  for(const face of mesh.faces){
    const pa = mesh.vertices[face[0]];
    const pb = mesh.vertices[face[1]];
    const pc = mesh.vertices[face[2]];
    const ppa = camera.projectPoint(pa, canvasWidth, canvasHeight);
    const ppb = camera.projectPoint(pb, canvasWidth, canvasHeight);
    const ppc = camera.projectPoint(pc, canvasWidth, canvasHeight);
    
    // Backface culling: check if triangle is facing away from camera
    const screenNormalZ = (ppb.x - ppa.x) * (ppc.y - ppa.y) - (ppb.y - ppa.y) * (ppc.x - ppa.x);
    if (screenNormalZ <= 0) continue; // Skip backfaces
    
    // Calculate face normal for lighting
    const v1 = pb.sub(pa);
    const v2 = pc.sub(pa);
    const normal = Vec3.cross(v1, v2);
    normal.normalize();
    
    // Directional light from upper right (sun-like)
    const sunDir = new Vec3(0.5, -0.7, 0.5);
    const sunDot = -Vec3.dot(normal, sunDir);
    
    // Ambient + directional lighting
    const ambient = 0.3;
    const diffuse = Math.max(0, sunDot);
    const brightness = Math.min(1.0, ambient + diffuse * 0.7);
    
    // Calculate if face should cast shadow (ground contact)
    const isBottom = normal.y < -0.9; // Bottom face facing down
    
    const avgDepth = ((ppa.depth||0)+(ppb.depth||0)+(ppc.depth||0))/3;
    projected.push({ pa:ppa, pb:ppb, pc:ppc, depth: avgDepth, brightness, isBottom });
  }
  // painter's sort back-to-front
  projected.sort((a,b) => b.depth - a.depth);
  ctx.save();
  for(const f of projected){
    if(!f.pa.visible && !f.pb.visible && !f.pc.visible) continue;
    ctx.beginPath();
    ctx.moveTo(f.pa.x, f.pa.y);
    ctx.lineTo(f.pb.x, f.pb.y);
    ctx.lineTo(f.pc.x, f.pc.y);
    ctx.closePath();
    if(style && style.fill) { 
      // Apply lighting to fill color
      const baseColor = style.fill;
      const shadedColor = shadeColor(baseColor, f.brightness);
      ctx.fillStyle = shadedColor;
      ctx.fill();
    }
    if(style && style.stroke && style.stroke !== 'transparent') { 
      ctx.strokeStyle = style.stroke; 
      ctx.lineWidth = 0.5;
      ctx.stroke(); 
    }
  }
  ctx.restore();
  
  // Return shadow projection data if requested
  if(castShadows) {
    return projected.filter(f => !f.isBottom).map(f => ({
      pa: f.pa, pb: f.pb, pc: f.pc
    }));
  }
}

// Helper to shade a hex color by a factor
function shadeColor(color, factor) {
  const hex = color.replace('#', '');
  let r = parseInt(hex.substr(0, 2), 16);
  let g = parseInt(hex.substr(2, 2), 16);
  let b = parseInt(hex.substr(4, 2), 16);
  
  r = Math.floor(r * factor);
  g = Math.floor(g * factor);
  b = Math.floor(b * factor);
  
  return '#' + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1);
}

// Draw soft contact shadows beneath meshes
function drawContactShadows(ctx, mesh, camera, canvasWidth, canvasHeight, groundHeight){
  const baseVertices = [];
  
  // Find vertices at ground level
  for(let i = 0; i < mesh.vertices.length; i++){
    const v = mesh.vertices[i];
    if(Math.abs(v.y - groundHeight) < 0.5){
      baseVertices.push(v);
    }
  }
  
  if(baseVertices.length < 3) return;
  
  // Project to screen
  const projected = baseVertices.map(v => camera.projectPoint(v, canvasWidth, canvasHeight));
  const visible = projected.filter(p => p.visible);
  
  if(visible.length < 3) return;
  
  // Draw soft shadow
  ctx.save();
  ctx.globalAlpha = 0.25;
  ctx.fillStyle = '#000000';
  ctx.beginPath();
  visible.forEach((p, i) => {
    if(i === 0) ctx.moveTo(p.x, p.y);
    else ctx.lineTo(p.x, p.y);
  });
  ctx.closePath();
  ctx.fill();
  ctx.restore();
}

// Expose API
if(typeof window !== 'undefined'){
  window.Renderer3D = window.Renderer3D || {};
  window.Renderer3D.Vec3 = Vec3;
  window.Renderer3D.Mat4 = Mat4;
  window.Renderer3D.Camera = Camera;
  window.Renderer3D.extrudePolygonToMesh = extrudePolygonToMesh;
  window.Renderer3D.drawMesh = drawMesh;
  window.Renderer3D.drawContactShadows = drawContactShadows;
}

// Node export
if(typeof module !== 'undefined' && module.exports){
  module.exports = { Vec3, Mat4, Camera, extrudePolygonToMesh, drawMesh };
}
