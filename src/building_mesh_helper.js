/**
 * Create a proper 3D building mesh from a 2D floor plan polygon
 * @param {Array<{x,y}>} floorPlan - 2D polygon vertices defining the building footprint
 * @param {number} height - Building height
 * @returns {{vertices: Vec3[], faces: number[][]}} - 3D mesh with vertices and triangulated faces
 */
function extrudeBuildingMesh(floorPlan, height) {
  if (!floorPlan || floorPlan.length < 3) {
    console.warn('Invalid floorPlan for building extrusion:', floorPlan);
    return { vertices: [], faces: [] };
  }

  const n = floorPlan.length;
  const vertices = [];
  const faces = [];

  // Step A: Create floor vertices (y=0) - BOTTOM of building sits on ground
  for (let i = 0; i < n; i++) {
    vertices.push(new window.Renderer3D.Vec3(floorPlan[i].x, 0, floorPlan[i].y));
  }

  // Step B: Create roof vertices (y=height) - TOP of building
  for (let i = 0; i < n; i++) {
    vertices.push(new window.Renderer3D.Vec3(floorPlan[i].x, height, floorPlan[i].y));
  }

  // Step C: Create VERTICAL WALL faces (one quad per edge = 2 triangles)
  for (let i = 0; i < n; i++) {
    const next = (i + 1) % n;
    const floorCurrent = i;          // Bottom vertex current
    const floorNext = next;          // Bottom vertex next
    const roofCurrent = n + i;       // Top vertex current
    const roofNext = n + next;       // Top vertex next

    // Wall quad as two triangles (counter-clockwise winding for outward-facing normals)
    faces.push([floorCurrent, floorNext, roofCurrent]);
    faces.push([floorNext, roofNext, roofCurrent]);
  }

  // Step D: Create FLOOR faces (bottom cap) - triangulate with simple fan
  // Winding: clockwise when viewed from below (so normal points down/inward)
  for (let i = 1; i < n - 1; i++) {
    faces.push([0, i + 1, i]);
  }

  // Step E: Create ROOF faces (top cap) - triangulate with simple fan  
  // Winding: counter-clockwise when viewed from above (so normal points up/outward)
  for (let i = 1; i < n - 1; i++) {
    faces.push([n, n + i, n + i + 1]);
  }

  return { vertices, faces };
}

// Expose to window
if (typeof window !== 'undefined') {
  window.extrudeBuildingMesh = extrudeBuildingMesh;
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = { extrudeBuildingMesh };
}
