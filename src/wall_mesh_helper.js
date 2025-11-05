// Helper to create proper wall meshes (hollow rings, not filled polygons)

function extrudeWallPath(wallPath, height, thickness) {
  const { Vec3 } = window.Renderer3D;
  const verts = [];
  const faces = [];
  
  const n = wallPath.length;
  
  // Create outer and inner vertices first
  const outerVerts = [];
  const innerVerts = [];
  
  for (let i = 0; i < n; i++) {
    const p = wallPath[i];
    const prevP = wallPath[(i - 1 + n) % n];
    const nextP = wallPath[(i + 1) % n];
    
    // Calculate incoming and outgoing edge directions
    const dx1 = p.x - prevP.x;
    const dy1 = p.y - prevP.y;
    const len1 = Math.sqrt(dx1 * dx1 + dy1 * dy1);
    
    const dx2 = nextP.x - p.x;
    const dy2 = nextP.y - p.y;
    const len2 = Math.sqrt(dx2 * dx2 + dy2 * dy2);
    
    // Calculate perpendiculars (pointing RIGHT relative to edge direction)
    // For a wall path going clockwise, this creates inward offset
    // For counter-clockwise, this creates outward offset
    let nx = 0, ny = 0;
    if (len1 > 0.01) {
      nx += dy1 / len1;  // Right perpendicular of incoming edge
      ny += -dx1 / len1;
    }
    if (len2 > 0.01) {
      nx += dy2 / len2;  // Right perpendicular of outgoing edge
      ny += -dx2 / len2;
    }
    
    const nlen = Math.sqrt(nx * nx + ny * ny);
    if (nlen > 0.01) {
      nx = nx / nlen * thickness;
      ny = ny / nlen * thickness;
    }
    
    outerVerts.push(p);
    innerVerts.push({ x: p.x + nx, y: p.y + ny });
  }
  
  // Create vertices (bottom and top for each point)
  for (let i = 0; i < n; i++) {
    const outer = outerVerts[i];
    const inner = innerVerts[i];
    
    verts.push(new Vec3(outer.x, 0, outer.y));        // Outer bottom
    verts.push(new Vec3(outer.x, height, outer.y));   // Outer top
    verts.push(new Vec3(inner.x, 0, inner.y));        // Inner bottom
    verts.push(new Vec3(inner.x, height, inner.y));   // Inner top
  }
  
  // Create faces
  for (let i = 0; i < n; i++) {
    const next = (i + 1) % n;
    const baseIdx = i * 4;
    const nextIdx = next * 4;
    
    // Outer wall face (2 triangles)
    faces.push([baseIdx + 0, baseIdx + 1, nextIdx + 1]);
    faces.push([baseIdx + 0, nextIdx + 1, nextIdx + 0]);
    
    // Inner wall face (2 triangles, reverse winding)
    faces.push([baseIdx + 2, nextIdx + 2, nextIdx + 3]);
    faces.push([baseIdx + 2, nextIdx + 3, baseIdx + 3]);
    
    // Top face (2 triangles)
    faces.push([baseIdx + 1, baseIdx + 3, nextIdx + 3]);
    faces.push([baseIdx + 1, nextIdx + 3, nextIdx + 1]);
    
    // Bottom face (2 triangles)
    faces.push([baseIdx + 0, nextIdx + 0, nextIdx + 2]);
    faces.push([baseIdx + 0, nextIdx + 2, baseIdx + 2]);
  }
  
  return { vertices: verts, faces };
}

if (typeof window !== 'undefined') {
  window.extrudeWallPath = extrudeWallPath;
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = { extrudeWallPath };
}
