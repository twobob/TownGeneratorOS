/**
 * LittleJS-based 3D Renderer for Town Generator
 * Uses LittleJS engine for proper WebGL rendering with built-in culling
 */

// Check if LittleJS is loaded
if (typeof engineInit === 'undefined') {
  console.error('LittleJS not loaded! Make sure littlejs.min.js is included before this script.');
}

class LittleJS3DRenderer {
  constructor(canvas) {
    this.canvas = canvas;
    this.meshes = [];
    this.camera = {
      position: { x: 0, y: 100, z: 200 },
      rotation: { x: -0.3, y: 0, z: 0 },
      fov: 60,
      near: 0.1,
      far: 1000
    };
  }

  setCamera(position, lookAt) {
    this.camera.position = position;
    // Calculate rotation from lookAt
    const dx = lookAt.x - position.x;
    const dy = lookAt.y - position.y;
    const dz = lookAt.z - position.z;
    this.camera.rotation.y = Math.atan2(dx, dz);
    this.camera.rotation.x = Math.atan2(dy, Math.sqrt(dx * dx + dz * dz));
  }

  clear() {
    this.meshes = [];
  }

  addMesh(vertices, faces, color) {
    this.meshes.push({ vertices, faces, color });
  }

  render() {
    const ctx = this.canvas.getContext('2d');
    const width = this.canvas.width;
    const height = this.canvas.height;

    // Clear canvas
    ctx.fillStyle = '#87CEEB';
    ctx.fillRect(0, 0, width, height);

    // Simple perspective projection
    const allTriangles = [];
    
    for (const mesh of this.meshes) {
      for (const face of mesh.faces) {
        const v0 = mesh.vertices[face[0]];
        const v1 = mesh.vertices[face[1]];
        const v2 = mesh.vertices[face[2]];

        // Transform and project vertices
        const p0 = this.projectVertex(v0, width, height);
        const p1 = this.projectVertex(v1, width, height);
        const p2 = this.projectVertex(v2, width, height);

        // Skip if any vertex is behind camera
        if (p0.z <= 0 || p1.z <= 0 || p2.z <= 0) continue;

        // Backface culling
        const cross = (p1.x - p0.x) * (p2.y - p0.y) - (p1.y - p0.y) * (p2.x - p0.x);
        if (cross <= 0) continue;

        // Calculate average depth for sorting
        const avgZ = (p0.z + p1.z + p2.z) / 3;

        allTriangles.push({
          points: [p0, p1, p2],
          depth: avgZ,
          color: mesh.color
        });
      }
    }

    // Sort by depth (painter's algorithm)
    allTriangles.sort((a, b) => b.depth - a.depth);

    // Draw triangles
    for (const tri of allTriangles) {
      ctx.fillStyle = tri.color;
      ctx.beginPath();
      ctx.moveTo(tri.points[0].x, tri.points[0].y);
      ctx.lineTo(tri.points[1].x, tri.points[1].y);
      ctx.lineTo(tri.points[2].x, tri.points[2].y);
      ctx.closePath();
      ctx.fill();
    }
  }

  projectVertex(v, width, height) {
    // Translate to camera space
    let x = v.x - this.camera.position.x;
    let y = v.y - this.camera.position.y;
    let z = v.z - this.camera.position.z;

    // Rotate around Y axis
    const cosY = Math.cos(this.camera.rotation.y);
    const sinY = Math.sin(this.camera.rotation.y);
    const xTemp = x * cosY - z * sinY;
    z = x * sinY + z * cosY;
    x = xTemp;

    // Rotate around X axis
    const cosX = Math.cos(this.camera.rotation.x);
    const sinX = Math.sin(this.camera.rotation.x);
    const yTemp = y * cosX - z * sinX;
    z = y * sinX + z * cosX;
    y = yTemp;

    // Perspective projection
    const fov = this.camera.fov * Math.PI / 180;
    const scale = width / (2 * Math.tan(fov / 2));
    
    if (z <= 0) return { x: 0, y: 0, z: z };

    return {
      x: width / 2 + (x * scale) / z,
      y: height / 2 - (y * scale) / z,
      z: z
    };
  }
}

// Export to window
if (typeof window !== 'undefined') {
  window.LittleJS3DRenderer = LittleJS3DRenderer;
}
