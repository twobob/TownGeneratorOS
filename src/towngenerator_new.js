/**
 * Medieval Fantasy City Generator - Pure JavaScript Implementation
 * No external dependencies - runs entirely in the browser
*  @author twobob @props Watabou 
*/

// ============================================================================
// Configuration Constants
// ============================================================================

const FLYTHROUGH_CONFIG = {
  CAMERA_HEIGHT: 6.0,        // Camera height above ground (roughly 6 feet)
  CAMERA_SPEED: 0.5,         // Movement speed (units per frame) - slower for first-person
  CAMERA_ZOOM: 30.0,         // Zoom level for first-person view (high zoom = ground level view)
  LOOK_AHEAD_DISTANCE: 5.0,  // How far ahead the camera looks
};

// 3D Rendering Configuration
const RENDER_3D_CONFIG = {
  NEAR_PLANE_CULL_THRESHOLD: 0.5  // View-space Z threshold for near-plane culling (positive = in front of camera)
                                   // Cull triangles with any vertex closer than this distance
                                   // Override in console: RENDER_3D_CONFIG.NEAR_PLANE_CULL_THRESHOLD = 1.0
};

// ============================================================================
// Utility Classes
// ============================================================================

class Random {
  static seed = 1;

  static reset(newSeed) {
    Random.seed = newSeed != null ? newSeed : Math.floor(Math.random() * 2147483647);
  }

  static float() {
    Random.seed = (Random.seed * 48271) % 2147483647;
    return Random.seed / 2147483647;
  }

  static int(min, max) {
    return Math.floor(min + Random.float() * (max - min));
  }

  static chance(probability) {
    return Random.float() < probability;
  }
}

class MathUtils {
  static sign(x) {
    return x < 0 ? -1 : (x > 0 ? 1 : 0);
  }

  static clamp(value, min, max) {
    return Math.min(Math.max(value, min), max);
  }
}

class Point {
  constructor(x = 0, y = 0) {
    this.x = x;
    this.y = y;
  }

  get length() {
    return Math.sqrt(this.x * this.x + this.y * this.y);
  }

  static distance(p1, p2) {
    const dx = p1.x - p2.x;
    const dy = p1.y - p2.y;
    return Math.sqrt(dx * dx + dy * dy);
  }

  clone() {
    return new Point(this.x, this.y);
  }

  set(other) {
    this.x = other.x;
    this.y = other.y;
  }
  
  static interpolate(p1, p2, t) {
    return new Point(
      p1.x + (p2.x - p1.x) * t,
      p1.y + (p2.y - p1.y) * t
    );
  }
}

// ============================================================================
// Geometry Classes
// ============================================================================

class Triangle {
  constructor(p1, p2, p3) {
    // Calculate signed area to ensure CCW ordering
    const s = (p2.x - p1.x) * (p2.y + p1.y) + (p3.x - p2.x) * (p3.y + p2.y) + (p1.x - p3.x) * (p1.y + p3.y);
    
    this.p1 = p1;
    this.p2 = s > 0 ? p2 : p3;
    this.p3 = s > 0 ? p3 : p2;
    
    // Calculate circumcenter using perpendicular bisector intersection
    const x1 = (this.p1.x + this.p2.x) / 2;
    const y1 = (this.p1.y + this.p2.y) / 2;
    const x2 = (this.p2.x + this.p3.x) / 2;
    const y2 = (this.p2.y + this.p3.y) / 2;
    
    const dx1 = this.p1.y - this.p2.y;
    const dy1 = this.p2.x - this.p1.x;
    const dx2 = this.p2.y - this.p3.y;
    const dy2 = this.p3.x - this.p2.x;
    
    // Check for degenerate case
    if (Math.abs(dx1) < 0.0001 || Math.abs(dy2 - dx2 * (dy1 / dx1)) < 0.0001) {
      // Fallback to centroid if lines are parallel
      this.c = new Point((p1.x + p2.x + p3.x) / 3, (p1.y + p2.y + p3.y) / 3);
      this.r = Point.distance(this.c, p1);
    } else {
      const tg1 = dy1 / dx1;
      const t2 = ((y1 - y2) - (x1 - x2) * tg1) / (dy2 - dx2 * tg1);
      
      this.c = new Point(x2 + dx2 * t2, y2 + dy2 * t2);
      this.r = Point.distance(this.c, this.p1);
    }
  }

  hasEdge(a, b) {
    return (this.p1 === a && this.p2 === b) || (this.p2 === a && this.p3 === b) ||
           (this.p3 === a && this.p1 === b);
  }
}

class Region {
  constructor(seed) {
    this.seed = seed;
    this.vertices = []; // Array of Triangle objects
  }

  center() {
    if (this.vertices.length === 0) return this.seed.clone();
    let cx = 0, cy = 0;
    for (const v of this.vertices) {
      cx += v.c.x;
      cy += v.c.y;
    }
    return new Point(cx / this.vertices.length, cy / this.vertices.length);
  }
}

class Voronoi {
  constructor(minx, miny, maxx, maxy) {
    this.triangles = [];
    
    const c1 = new Point(minx, miny);
    const c2 = new Point(minx, maxy);
    const c3 = new Point(maxx, miny);
    const c4 = new Point(maxx, maxy);
    
    this.frame = [c1, c2, c3, c4];
    this.points = [c1, c2, c3, c4];
    
    this.triangles.push(new Triangle(c1, c2, c3));
    this.triangles.push(new Triangle(c2, c3, c4));
  }

  static build(vertices) {
    let minx = Infinity, miny = Infinity;
    let maxx = -Infinity, maxy = -Infinity;
    
    for (const v of vertices) {
      if (v.x < minx) minx = v.x;
      if (v.y < miny) miny = v.y;
      if (v.x > maxx) maxx = v.x;
      if (v.y > maxy) maxy = v.y;
    }
    
    const dx = (maxx - minx) * 0.5;
    const dy = (maxy - miny) * 0.5;
    const voronoi = new Voronoi(minx - dx / 2, miny - dy / 2, maxx + dx / 2, maxy + dy / 2);
    
    for (const v of vertices) {
      voronoi.addPoint(v);
    }
    
    return voronoi;
  }

  static relax(voronoi, toRelax) {
    const regions = voronoi.partitioning();
    const newPoints = [];
    
    for (const r of regions) {
      if (toRelax && toRelax.includes(r.seed)) {
        newPoints.push(r.center());
      } else if (!voronoi.frame.includes(r.seed)) {
        newPoints.push(r.seed);
      }
    }
    
    return Voronoi.build(newPoints);
  }

  addPoint(p) {
    const toSplit = [];
    
    for (const tr of this.triangles) {
      if (Point.distance(p, tr.c) < tr.r + 0.001) {
        toSplit.push(tr);
      }
    }
    
    if (toSplit.length === 0) return;
    
    this.points.push(p);
    
    const edges = [];
    for (const t1 of toSplit) {
      const checkEdge = (a, b) => {
        let isOuter = true;
        for (const t2 of toSplit) {
          if (t2 !== t1 && t2.hasEdge(b, a)) {
            isOuter = false;
            break;
          }
        }
        if (isOuter) edges.push([a, b]);
      };
      
      checkEdge(t1.p1, t1.p2);
      checkEdge(t1.p2, t1.p3);
      checkEdge(t1.p3, t1.p1);
    }
    
    this.triangles = this.triangles.filter(tr => !toSplit.includes(tr));
    
    for (const [a, b] of edges) {
      this.triangles.push(new Triangle(p, a, b));
    }
  }

  buildRegion(p) {
    const r = new Region(p);
    
    // Collect triangles that include this point (like original Haxe)
    for (const tr of this.triangles) {
      if (tr.p1 === p || tr.p2 === p || tr.p3 === p) {
        r.vertices.push(tr);
      }
    }
    
    // Sort triangles by angle of their circumcenters around seed point
    r.vertices.sort((v1, v2) => {
      const x1 = v1.c.x - p.x;
      const y1 = v1.c.y - p.y;
      const x2 = v2.c.x - p.x;
      const y2 = v2.c.y - p.y;
      
      if (x1 >= 0 && x2 < 0) return 1;
      if (x2 >= 0 && x1 < 0) return -1;
      if (x1 === 0 && x2 === 0) return y2 > y1 ? 1 : -1;
      
      return MathUtils.sign(x2 * y1 - x1 * y2);
    });
    
    return r;
  }

  partitioning() {
    const regions = [];
    for (const p of this.points) {
      if (!this.frame.includes(p)) {
        const r = this.buildRegion(p);
        
        // Check if all triangles in this region are "real" (don't touch frame)
        let isReal = true;
        for (const tr of r.vertices) {
          if (this.frame.includes(tr.p1) || this.frame.includes(tr.p2) || this.frame.includes(tr.p3)) {
            isReal = false;
            break;
          }
        }
        
        if (isReal) {
          regions.push(r);
        }
      }
    }
    return regions;
  }
}

class Polygon {
  static distance(poly, point) {
    if (poly.length === 0) return Infinity;
    let minDist = Infinity;
    for (const p of poly) {
      const d = Point.distance(p, point);
      if (d < minDist) minDist = d;
    }
    return minDist;
  }

  static findEdge(poly, a, b) {
    for (let i = 0; i < poly.length; i++) {
      const j = (i + 1) % poly.length;
      if (poly[i] === a && poly[j] === b) return i;
    }
    return -1;
  }

  static centroid(polygon) {
    if (!polygon || polygon.length === 0) return {x: 0, y: 0};
    const center = polygon.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= polygon.length;
    center.y /= polygon.length;
    return center;
  }
}

// ============================================================================
// City Generation
// ============================================================================

class Patch {
  constructor(shape) {
    this.shape = shape;
    this.withinCity = false;
    this.withinWalls = false;
    this.ward = null;
  }

  static fromRegion(region) {
    // Extract circumcenters from triangle vertices
    const vertices = region.vertices.map(tr => tr.c);
    return new Patch(vertices);
  }
}

class Ward {
  constructor(model, patch, wardType = 'craftsmen') {
    this.model = model;
    this.patch = patch;
    this.shape = patch.shape;
    this.geometry = [];
    this.wardType = wardType;
  }

  buildGeometry() {
    // Recursively subdivide ward into building plots (like original Haxe)
    const minSq = 20;
    const gridChaos = this.model.gridChaos || 0.2;
    const sizeChaos = this.model.sizeChaos || 0.3;
    
    // Random chance to create an open piazza instead of buildings
    if (Random.chance(StateManager.plazaChance)) {
      // Create piazza with buildings around perimeter and empty center
      this.geometry = this.createPiazza(this.shape);
    } else {
      // Normal ward with buildings
      this.geometry = this.createAlleys(this.shape, minSq, gridChaos, sizeChaos, true);
    }
  }

  createPiazza(polygon) {
    // Create ring of buildings around the perimeter with open center
    const buildings = [];
    const minSq = 20;
    const gridChaos = this.model.gridChaos || 0.2;
    const sizeChaos = this.model.sizeChaos || 0.3;
    
    // Calculate center
    const center = polygon.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= polygon.length;
    center.y /= polygon.length;
    
    // Create inner ring (60-75% of original size)
    const innerScale = 0.6 + Random.float() * 0.15;
    const innerRing = polygon.map(p => new Point(
      center.x + (p.x - center.x) * innerScale,
      center.y + (p.y - center.y) * innerScale
    ));
    
    // Create building strips between outer and inner rings, then subdivide each strip
    for (let i = 0; i < polygon.length; i++) {
      const j = (i + 1) % polygon.length;
      
      // Outer edge
      const outerA = polygon[i];
      const outerB = polygon[j];
      
      // Inner edge
      const innerA = innerRing[i];
      const innerB = innerRing[j];
      
      // Create strip quad between rings
      const strip = [outerA, outerB, innerB, innerA];
      
      // Subdivide this strip into buildings using the alley logic
      const stripBuildings = this.createAlleys(strip, minSq, gridChaos, sizeChaos, true);
      buildings.push(...stripBuildings);
    }
    
    // Optionally add small central feature
    if (Random.chance(0.3)) {
      const featureSize = 1.5 + Random.float() * 1.5;
      const isCircular = Random.chance(0.5);
      
      if (isCircular) {
        const segments = 12;
        const feature = [];
        for (let i = 0; i < segments; i++) {
          const angle = (i / segments) * Math.PI * 2;
          feature.push(new Point(
            center.x + Math.cos(angle) * featureSize,
            center.y + Math.sin(angle) * featureSize
          ));
        }
        buildings.push(feature);
      } else {
        const angle = Random.float() * Math.PI * 0.5;
        const cos = Math.cos(angle);
        const sin = Math.sin(angle);
        buildings.push([
          new Point(center.x - featureSize*cos + featureSize*sin, center.y - featureSize*sin - featureSize*cos),
          new Point(center.x + featureSize*cos + featureSize*sin, center.y + featureSize*sin - featureSize*cos),
          new Point(center.x + featureSize*cos - featureSize*sin, center.y + featureSize*sin + featureSize*cos),
          new Point(center.x - featureSize*cos - featureSize*sin, center.y - featureSize*sin + featureSize*cos)
        ]);
      }
    }
    
    return buildings;
  }

  createAlleys(polygon, minSq, gridChaos, sizeChaos, split) {
    // Find longest edge
    let longestIdx = 0;
    let maxLength = 0;
    for (let i = 0; i < polygon.length; i++) {
      const p0 = polygon[i];
      const p1 = polygon[(i + 1) % polygon.length];
      const len = Point.distance(p0, p1);
      if (len > maxLength) {
        maxLength = len;
        longestIdx = i;
      }
    }

    const v0 = polygon[longestIdx];
    const v1 = polygon[(longestIdx + 1) % polygon.length];
    
    // Split ratio with chaos
    const spread = 0.8 * gridChaos;
    const ratio = (1 - spread) / 2 + Random.float() * spread;
    
    // Angle variation
    const angleSpread = Math.PI / 6 * gridChaos;
    const angleOffset = (Random.float() - 0.5) * angleSpread;
    
    const splitX = v0.x + (v1.x - v0.x) * ratio;
    const splitY = v0.y + (v1.y - v0.y) * ratio;
    
    // Perpendicular direction with angle offset
    const dx = v1.x - v0.x;
    const dy = v1.y - v0.y;
    const len = Math.sqrt(dx * dx + dy * dy);
    if (len < 0.1) return [];
    
    const nx = dx / len;
    const ny = dy / len;
    const perpX = -ny * Math.cos(angleOffset) - nx * Math.sin(angleOffset);
    const perpY = nx * Math.cos(angleOffset) - ny * Math.sin(angleOffset);
    
    // Cut with alley gap
    const alleyWidth = split ? (this.model.alleyWidth || 0.6) : 0;
    const cutP1 = new Point(splitX, splitY);
    const cutP2 = new Point(splitX + perpX * 1000, splitY + perpY * 1000);
    
    const halves = this.cutPolygon(polygon, cutP1, cutP2, alleyWidth);
    
    const buildings = [];
    for (const half of halves) {
      const area = this.polygonArea(half);
      const sizeVariation = Math.pow(2, 4 * sizeChaos * (Random.float() - 0.5));
      if (area < minSq * sizeVariation) {
        // Small enough - make it a building (skip some for empty lots)
        if (Random.float() > 0.04) {
          buildings.push(half);
        }
      } else {
        // Keep subdividing
        const shouldSplit = area > minSq / (Random.float() * Random.float());
        buildings.push(...this.createAlleys(half, minSq, gridChaos, sizeChaos, shouldSplit));
      }
    }
    
    return buildings;
  }

  cutPolygon(poly, p1, p2, gap = 0) {
    // Simple polygon cutting - returns two halves with optional gap
    const x1 = p1.x, y1 = p1.y;
    const dx1 = p2.x - x1, dy1 = p2.y - y1;
    const len = Math.sqrt(dx1 * dx1 + dy1 * dy1);
    
    // Perpendicular vector for gap
    const perpX = -dy1 / len;
    const perpY = dx1 / len;
    
    const intersections = [];
    for (let i = 0; i < poly.length; i++) {
      const v0 = poly[i];
      const v1 = poly[(i + 1) % poly.length];
      
      const x2 = v0.x, y2 = v0.y;
      const dx2 = v1.x - x2, dy2 = v1.y - y2;
      
      const denom = dx1 * dy2 - dy1 * dx2;
      if (Math.abs(denom) > 0.001) {
        const t = ((x2 - x1) * dy2 - (y2 - y1) * dx2) / denom;
        const u = ((x2 - x1) * dy1 - (y2 - y1) * dx1) / denom;
        
        if (u >= 0 && u <= 1) {
          const intPoint = new Point(x1 + dx1 * t, y1 + dy1 * t);
          intersections.push({
            point: intPoint,
            point1: new Point(intPoint.x - perpX * gap / 2, intPoint.y - perpY * gap / 2),
            point2: new Point(intPoint.x + perpX * gap / 2, intPoint.y + perpY * gap / 2),
            index: i
          });
        }
      }
    }
    
    if (intersections.length !== 2) return [poly];
    
    const [int1, int2] = intersections;
    const half1 = [];
    const half2 = [];
    
    for (let i = 0; i <= int1.index; i++) {
      half1.push(poly[i]);
    }
    half1.push(gap > 0 ? int1.point1 : int1.point);
    half1.push(gap > 0 ? int2.point1 : int2.point);
    for (let i = int2.index + 1; i < poly.length; i++) {
      half1.push(poly[i]);
    }
    
    half2.push(gap > 0 ? int1.point2 : int1.point);
    for (let i = int1.index + 1; i <= int2.index; i++) {
      half2.push(poly[i]);
    }
    half2.push(gap > 0 ? int2.point2 : int2.point);
    
    return [half1, half2].filter(h => h.length >= 3);
  }

  polygonArea(poly) {
    let area = 0;
    for (let i = 0; i < poly.length; i++) {
      const j = (i + 1) % poly.length;
      area += poly[i].x * poly[j].y;
      area -= poly[j].x * poly[i].y;
    }
    return Math.abs(area / 2);
  }

  getCenter() {
    if (this.shape.length === 0) return new Point(0, 0);
    let cx = 0, cy = 0;
    for (const p of this.shape) {
      cx += p.x;
      cy += p.y;
    }
    return new Point(cx / this.shape.length, cy / this.shape.length);
  }

  getRadius() {
    const center = this.getCenter();
    let maxDist = 0;
    for (const p of this.shape) {
      const d = Point.distance(p, center);
      if (d > maxDist) maxDist = d;
    }
    return maxDist;
  }

  getLabel() {
    const labels = {
      'craftsmen': 'Craftsmen Ward',
      'merchant': 'Merchant Ward',
      'slum': 'Slums',
      'patriciate': 'Patriciate Ward',
      'administration': 'Administration',
      'military': 'Military Ward',
      'park': 'Park'
    };
    return labels[this.wardType] || 'Ward';
  }
}

// Special ward types
class Plaza extends Ward {
  buildGeometry() {
    // Plaza is an EMPTY open square - no buildings at all!
    this.geometry = [];
  }
  
  getLabel() {
    return 'Plaza';
  }
}

class Castle extends Ward {
  buildGeometry() {
    // Citadel with defensive walls, towers, and gate
    const center = this.shape.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= this.shape.length;
    center.y /= this.shape.length;
    
    this.geometry = [];
    
    // Inner citadel wall (thick defensive perimeter)
    const innerWall = this.shrinkPolygon(this.shape, 3);
    this.citadelWall = innerWall;
    
    // Add corner towers
    const towerSize = 3;
    const towers = [];
    for (let i = 0; i < innerWall.length; i++) {
      const v = innerWall[i];
      const prev = innerWall[(i - 1 + innerWall.length) % innerWall.length];
      const next = innerWall[(i + 1) % innerWall.length];
      
      // Calculate angle at this vertex
      const dx1 = v.x - prev.x, dy1 = v.y - prev.y;
      const dx2 = next.x - v.x, dy2 = next.y - v.y;
      const angle1 = Math.atan2(dy1, dx1);
      const angle2 = Math.atan2(dy2, dx2);
      const angleDiff = Math.abs(angle1 - angle2);
      
      // Place tower at corners (where angle changes significantly)
      if (angleDiff > 0.5 || i % Math.max(2, Math.floor(innerWall.length / 4)) === 0) {
        const segments = 8;
        const tower = [];
        for (let j = 0; j < segments; j++) {
          const a = (j / segments) * Math.PI * 2;
          tower.push(new Point(v.x + Math.cos(a) * towerSize, v.y + Math.sin(a) * towerSize));
        }
        towers.push(tower);
      }
    }
    
    // Find gate position (towards center of city)
    const cityCenter = new Point(0, 0);
    let gateVertex = innerWall[0];
    let maxDist = -Infinity;
    for (const v of innerWall) {
      const dist = Point.distance(v, cityCenter);
      if (dist > maxDist) {
        maxDist = dist;
        gateVertex = v;
      }
    }
    this.citadelGate = gateVertex;
    
    // Inner keep buildings
    const keep = this.shrinkPolygon(innerWall, 8);
    const buildings = this.createAlleys(keep, 15, 0.1, 0.1, Random.chance(0.4));
    
    this.geometry = [...buildings, ...towers];
  }

  shrinkPolygon(poly, amount) {
    const center = poly.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= poly.length;
    center.y /= poly.length;
    const factor = 1 - (amount * 0.05);
    return poly.map(p => new Point(
      center.x + (p.x - center.x) * factor,
      center.y + (p.y - center.y) * factor
    ));
  }

  getLabel() {
    return 'Castle';
  }
}

class Cathedral extends Ward {
  buildGeometry() {
    const shrunkBlock = this.shrinkPolygon(this.shape, 4);
    if (Random.chance(0.4)) {
      this.geometry = this.createRing(shrunkBlock);
    } else {
      this.geometry = this.createAlleys(shrunkBlock, 20, 0.1, 0.1, Random.chance(0.8));
    }
  }

  shrinkPolygon(poly, amount) {
    const center = poly.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= poly.length;
    center.y /= poly.length;
    const factor = 1 - (amount * 0.05);
    return poly.map(p => new Point(
      center.x + (p.x - center.x) * factor,
      center.y + (p.y - center.y) * factor
    ));
  }

  createRing(block) {
    const center = block.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= block.length;
    center.y /= block.length;
    
    const outer = block.map(p => new Point(
      center.x + (p.x - center.x) * 0.9,
      center.y + (p.y - center.y) * 0.9
    ));
    const inner = block.map(p => new Point(
      center.x + (p.x - center.x) * 0.6,
      center.y + (p.y - center.y) * 0.6
    ));
    
    return [outer, inner];
  }

  getLabel() {
    return 'Temple';
  }
}

class Market extends Ward {
  buildGeometry() {
    const statue = Random.chance(0.6);
    const center = this.shape.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= this.shape.length;
    center.y /= this.shape.length;
    
    let object;
    if (statue) {
      const w = 1 + Random.float();
      const h = 1 + Random.float();
      const angle = Random.float() * Math.PI * 2;
      const cos = Math.cos(angle);
      const sin = Math.sin(angle);
      object = [
        new Point(center.x - w*cos + h*sin, center.y - w*sin - h*cos),
        new Point(center.x + w*cos + h*sin, center.y + w*sin - h*cos),
        new Point(center.x + w*cos - h*sin, center.y + w*sin + h*cos),
        new Point(center.x - w*cos - h*sin, center.y - w*sin + h*cos)
      ];
    } else {
      const r = 1 + Random.float();
      const segments = 12;
      object = [];
      for (let i = 0; i < segments; i++) {
        const angle = (i / segments) * Math.PI * 2;
        object.push(new Point(center.x + Math.cos(angle) * r, center.y + Math.sin(angle) * r));
      }
    }
    
    this.geometry = [object];
  }

  getLabel() {
    return 'Market';
  }
}

class Park extends Ward {
  buildGeometry() {
    // Parks have green space with smoothed outline (using Chaikin algorithm approximation)
    this.geometry = [];
    this.green = null;
    this.trees = null;
    
    // Get available area
    const available = this.shape;
    
    // Create smoothed green area outline by adding interpolated points
    const points = [];
    for (let i = 0; i < available.length; i++) {
      const current = available[i];
      const next = available[(i + 1) % available.length];
      
      // Add current point
      points.push(current);
      // Add interpolated point (lerp) between current and next
      points.push(Point.interpolate(current, next, 0.5));
    }
    
    // Apply Chaikin smoothing algorithm (3 iterations as in MFCG)
    let smoothed = points.slice();
    const iterations = 3;
    
    for (let iter = 0; iter < iterations; iter++) {
      const newSmoothed = [];
      const len = smoothed.length;
      
      for (let i = 0; i < len; i++) {
        const curr = smoothed[i];
        const next = smoothed[(i + 1) % len];
        
        // Chaikin: Q = 3/4 * curr + 1/4 * next
        //          R = 1/4 * curr + 3/4 * next
        newSmoothed.push(new Point(
          0.75 * curr.x + 0.25 * next.x,
          0.75 * curr.y + 0.25 * next.y
        ));
        newSmoothed.push(new Point(
          0.25 * curr.x + 0.75 * next.x,
          0.25 * curr.y + 0.75 * next.y
        ));
      }
      smoothed = newSmoothed;
    }
    
    this.green = smoothed;
    this.geometry = []; // Parks don't have building geometry, just green space
    this.trees = null; // Trees spawned lazily
  }
  
  spawnTrees() {
    // Lazy tree generation using MFCG algorithm
    if (this.trees !== null) return this.trees;
    
    this.trees = [];
    if (!this.shape || this.shape.length < 3) return this.trees;
    
    // Use Poisson disk sampling to fill the park area with tree positions
    // Greenery density for parks (higher than regular wards)
    const greeneryDensity = 0.7; // Parks are ~70% filled with trees
    
    // Fill the available area (shape) with points using pattern
    const points = this.fillAreaWithPattern(this.shape);
    
    // Filter points using noise and density
    for (const point of points) {
      // Use Perlin noise to create natural-looking tree distribution
      const noiseValue = (PerlinNoise.noise(point.x * 0.05, point.y * 0.05) + 1) / 2;
      if (noiseValue < greeneryDensity) {
        // Create tree with crown polygon like MFCG
        this.trees.push({
          pos: point,
          crown: this.getTreeCrown()
        });
      }
    }
    
    return this.trees;
  }
  
  fillAreaWithPattern(polygon) {
    // Simplified Poisson disk sampling for polygon
    // MFCG uses distance ~2.25 units between points
    const spacing = 3.0;
    const points = [];
    
    // Get bounding box
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const p of polygon) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x);
      maxY = Math.max(maxY, p.y);
    }
    
    // Grid-based sampling with jitter
    for (let y = minY; y < maxY; y += spacing) {
      for (let x = minX; x < maxX; x += spacing) {
        // Add jitter for more natural distribution
        const jitterX = (Random.float() - 0.5) * spacing * 0.5;
        const jitterY = (Random.float() - 0.5) * spacing * 0.5;
        const point = new Point(x + jitterX, y + jitterY);
        
        // Check if point is inside polygon
        if (this.isPointInPolygon(point, polygon)) {
          points.push(point);
        }
      }
    }
    
    return points;
  }
  
  getTreeCrown() {
    // Generate a random tree crown polygon (MFCG implementation)
    // Random radius variation: 1.5 * pow(1.5, gaussian(-1 to 1))
    const r1 = Random.float();
    const r2 = Random.float();
    const r3 = Random.float();
    const gaussian = (r1 + r2 + r3) / 3 * 2 - 1; // Approximate gaussian
    const radius = 1.5 * Math.pow(1.5, gaussian);
    
    // Create 6-pointed irregular polygon
    const crown = [];
    for (let i = 0; i < 6; i++) {
      const angleOffset = (Random.float() + Random.float() + Random.float()) / 3;
      const angle = 2 * Math.PI * (i + angleOffset) / 6;
      
      // Radius variation
      const r4 = Random.float();
      const r5 = Random.float();
      const r6 = Random.float();
      const r7 = Random.float();
      const radiusVar = Math.abs((r4 + r5 + r6 + r7) / 2 - 1);
      const pointRadius = radius * (1 - 4/6 * radiusVar);
      
      crown.push({
        x: Math.cos(angle) * pointRadius,
        y: Math.sin(angle) * pointRadius
      });
    }
    
    return crown;
  }
  
  isPointInPolygon(point, polygon) {
    // Ray casting algorithm for point-in-polygon test
    let inside = false;
    for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
      const xi = polygon[i].x, yi = polygon[i].y;
      const xj = polygon[j].x, yj = polygon[j].y;
      
      const intersect = ((yi > point.y) !== (yj > point.y))
          && (point.x < (xj - xi) * (point.y - yi) / (yj - yi) + xi);
      if (intersect) inside = !inside;
    }
    return inside;
  }

  getLabel() {
    return 'Park';
  }
}

// Initialize Perlin noise for tree distribution if not already done
if (typeof PerlinNoise === 'undefined') {
  var PerlinNoise = {
    noise: function(x, y) {
      // Simple Perlin-like noise using sin waves
      return Math.sin(x * 2.1) * Math.cos(y * 1.7) + 
             Math.sin(x * 1.3 + y * 2.3) * 0.5 +
             Math.sin((x + y) * 0.7) * 0.25;
    }
  };
}

class Slum extends Ward {
  buildGeometry() {
    // Slums have dense, irregular buildings with narrow alleys
    // More chaotic than normal wards
    const shrunkBlock = this.shrinkPolygon(this.shape, 2);
    
    // Create very dense alleys with small buildings
    this.geometry = this.createAlleys(
      shrunkBlock,
      8,      // Smaller building size
      0.05,   // Very narrow gaps
      0.15,   // More irregular
      Random.chance(0.3) // Less likely to be rectangular
    );
  }

  shrinkPolygon(poly, amount) {
    const center = poly.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= poly.length;
    center.y /= poly.length;
    const factor = 1 - (amount * 0.05);
    return poly.map(p => new Point(
      center.x + (p.x - center.x) * factor,
      center.y + (p.y - center.y) * factor
    ));
  }

  getLabel() {
    return 'Slum';
  }
}

class Farm extends Ward {
  buildGeometry() {
    // Generate farm fields with furrows
    this.subPlots = [];
    this.furrows = [];
    this.buildings = [];
    
    // Small farmhouse building
    const center = this.shape.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= this.shape.length;
    center.y /= this.shape.length;
    
    // Random vertex for positioning
    const randomVertex = this.shape[Random.int(0, this.shape.length)];
    const pos = Point.interpolate(randomVertex, center, 0.3 + Random.float() * 0.4);
    
    // Small rectangular housing
    const size = 4;
    const angle = Random.float() * Math.PI;
    const cos = Math.cos(angle);
    const sin = Math.sin(angle);
    
    const housing = [
      new Point(pos.x - cos * size - sin * size, pos.y - sin * size + cos * size),
      new Point(pos.x - cos * size + sin * size, pos.y - sin * size - cos * size),
      new Point(pos.x + cos * size + sin * size, pos.y + sin * size - cos * size),
      new Point(pos.x + cos * size - sin * size, pos.y + sin * size + cos * size)
    ];
    
    this.buildings = [housing];
    this.geometry = [housing];
    
    // Create subplot (the whole farm field)
    this.subPlots = [this.shape];
    
    // Generate furrows (plowed lines) across the farm
    if (Random.chance(0.7)) { // 70% chance of furrows
      const bounds = this.getBounds();
      const furrowSpacing = 2 + Random.float() * 2;
      const furrowAngle = Random.float() * Math.PI;
      
      for (let i = 0; i < bounds.width / furrowSpacing; i++) {
        const offset = i * furrowSpacing;
        const startX = bounds.x + offset;
        const startY = bounds.y;
        const endX = bounds.x + offset;
        const endY = bounds.y + bounds.height;
        
        // Rotate furrow
        const cx = bounds.x + bounds.width / 2;
        const cy = bounds.y + bounds.height / 2;
        const cos = Math.cos(furrowAngle);
        const sin = Math.sin(furrowAngle);
        
        const start = new Point(
          cx + (startX - cx) * cos - (startY - cy) * sin,
          cy + (startX - cx) * sin + (startY - cy) * cos
        );
        const end = new Point(
          cx + (endX - cx) * cos - (endY - cy) * sin,
          cy + (endX - cx) * sin + (endY - cy) * cos
        );
        
        this.furrows.push({ start, end });
      }
    }
  }
  
  getBounds() {
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const p of this.shape) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x);
      maxY = Math.max(maxY, p.y);
    }
    return { x: minX, y: minY, width: maxX - minX, height: maxY - minY };
  }
  
  getLabel() {
    return 'Farm';
  }
}

class CityModel {
  static instance = null;

  constructor(nPatches, seed) {
    this.nPatches = Math.max(nPatches || 15, 4); // Minimum 4 patches to avoid edge cases
    
    if (seed > 0) {
      Random.reset(seed);
    }
    
    this.plazaNeeded = StateManager.plazaNeeded;
    this.citadelNeeded = StateManager.citadelNeeded;
    this.wallsNeeded = StateManager.wallsNeeded;
    this.gridChaos = StateManager.gridChaos;
    this.sizeChaos = StateManager.sizeChaos;
    this.alleyWidth = StateManager.alleyWidth;
    this.buildingGap = StateManager.buildingGap;
    
    this.patches = [];
    this.inner = [];
    this.streets = [];
    this.gates = [];
    
    try {
      this.build();
      CityModel.instance = this;
    } catch (e) {
      console.error('City generation failed:', e);
      CityModel.instance = null;
    }
  }

  build() {
    this.buildPatches();
    this.buildWalls();
    this.buildStreets();
    this.createWards();
    this.buildGeometry();
  }

  buildPatches() {
    const sa = Random.float() * 2 * Math.PI;
    const points = [];
    const cellChaos = StateManager.cellChaos || 0.0;
    
    for (let i = 0; i < this.nPatches * 8; i++) {
      const a = sa + Math.sqrt(i) * 5;
      // Add cell chaos variation to radius
      const baseR = i === 0 ? 0 : 10 + i * (2 + Random.float());
      const chaosOffset = cellChaos * (Random.float() - 0.5) * baseR * 0.5;
      const r = baseR + chaosOffset;
      points.push(new Point(Math.cos(a) * r, Math.sin(a) * r));
    }
    
    let voronoi = Voronoi.build(points);
    
    const relaxIndices = [0, 1, 2, this.nPatches];
    
    for (let i = 0; i < 3; i++) {
      const toRelax = Array.from(new Set(relaxIndices
        .map(index => voronoi.points[index])
        .filter(point => point != null)
      ));

      voronoi = Voronoi.relax(voronoi, toRelax);
    }
    
    voronoi.points.sort((p1, p2) => MathUtils.sign(p1.length - p2.length));
    
    const regions = voronoi.partitioning();
    
    let count = 0;
    for (const r of regions) {
      const patch = Patch.fromRegion(r);
      this.patches.push(patch);
      
      if (count === 0) {
        this.center = patch.shape.reduce((min, p) => 
          p.length < min.length ? p : min
        );
        
        if (this.plazaNeeded) {
          this.plaza = patch;
        }
      } else if (count === this.nPatches && this.citadelNeeded) {
        this.citadel = patch;
        this.citadel.withinCity = true;
      }
      
      if (count < this.nPatches) {
        patch.withinCity = true;
        patch.withinWalls = this.wallsNeeded;
        this.inner.push(patch);
      }
      
      count++;
    }
    
    this.cityRadius = 0;
    for (const patch of this.inner) {
      for (const p of patch.shape) {
        const d = p.length;
        if (d > this.cityRadius) this.cityRadius = d;
      }
    }
  }

  isPointInPolygon(point, polygon) {
    if (polygon.length < 3) return false;
    
    // Ray casting algorithm
    let inside = false;
    for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
      const xi = polygon[i].x, yi = polygon[i].y;
      const xj = polygon[j].x, yj = polygon[j].y;
      
      const intersect = ((yi > point.y) !== (yj > point.y))
        && (point.x < (xj - xi) * (point.y - yi) / (yj - yi) + xi);
      if (intersect) inside = !inside;
    }
    return inside;
  }

  buildWalls() {
    if (this.inner.length === 0) {
      this.borderShape = [];
      return;
    }
    
    if (this.inner.length === 1) {
      this.borderShape = [...this.inner[0].shape];
      return;
    }
    
    // Use the exact same logic as Haxe Model.findCircumference
    const A = [];
    const B = [];
    
    for (const w1 of this.inner) {
      for (let i = 0; i < w1.shape.length; i++) {
        const a = w1.shape[i];
        const b = w1.shape[(i + 1) % w1.shape.length];
        
        let outerEdge = true;
        for (const w2 of this.inner) {
          if (Polygon.findEdge(w2.shape, b, a) !== -1) {
            outerEdge = false;
            break;
          }
        }
        
        if (outerEdge) {
          A.push(a);
          B.push(b);
        }
      }
    }
    
    // Chain edges together
    this.borderShape = [];
    if (A.length > 0) {
      let index = 0;
      let iterations = 0;
      const maxIterations = A.length + 10; // Safety limit
      
      do {
        this.borderShape.push(A[index]);
        index = A.indexOf(B[index]);
        iterations++;
        
        if (iterations > maxIterations) {
          console.warn('Wall chaining exceeded max iterations, breaking');
          break;
        }
      } while (index !== 0 && index !== -1 && iterations < maxIterations);
    }
    
    // Mark patches where MAJORITY of vertices are inside the wall
    for (const patch of this.patches) {
      if (!patch.withinCity && this.borderShape.length > 0) {
        let verticesInside = 0;
        for (const vertex of patch.shape) {
          if (this.isPointInPolygon(vertex, this.borderShape)) {
            verticesInside++;
          }
        }
        if (verticesInside >= patch.shape.length / 2) {
          patch.withinCity = true;
        }
      }
    }
    
    // Generate gates
    if (this.wallsNeeded && this.borderShape.length > 0) {
      const numGates = 2 + Random.int(0, 3);
      for (let i = 0; i < numGates; i++) {
        const idx = Random.int(0, this.borderShape.length);
        this.gates.push(this.borderShape[idx]);
      }
    }
    
    // Filter patches to reasonable radius
    const radius = this.cityRadius;
    this.patches = this.patches.filter(p => {
      return Polygon.distance(p.shape, this.center) < radius * 3;
    });
  }

  buildStreets() {
    // console.log('buildStreets() called');
    // console.log('Gates:', this.gates ? this.gates.length : 0);
    // console.log('Plaza:', this.plaza ? 'exists' : 'none');
    // console.log('Border shape:', this.borderShape ? this.borderShape.length : 0);
    
    // Build topology graph for pathfinding
    const topology = this.buildTopology();
    
    // Determine street target based on what's available
    let streetTarget = null;
    let targetVertices = [];
    
    if (this.plaza && this.plaza.shape) {
      // Use plaza vertices as targets
      targetVertices = this.plaza.shape;
      // console.log('Using plaza vertices as targets:', targetVertices.length);
    } else {
      // No plaza: aim for city center or nearest cell boundary to center
      const center = new Point(0, 0);
      
      // Collect all vertices from topology that are closest to center
      for (const vertex of topology.keys()) {
        targetVertices.push(vertex);
      }
      
      // Sort by distance to center and take closest ones
      targetVertices.sort((a, b) => {
        const distA = Point.distance(a, center);
        const distB = Point.distance(b, center);
        return distA - distB;
      });
      
      // Use top 4 closest vertices as targets
      targetVertices = targetVertices.slice(0, 4);
      // console.log('No plaza - using closest vertices to center as targets:', targetVertices.length);
    }
    
    // Get gates or create virtual gates if walls disabled
    let gatePoints = this.gates;
    
    if (gatePoints.length === 0 && this.borderShape && this.borderShape.length > 0) {
      // console.log('No gates found - creating virtual gates');
      // No gates (walls disabled): create virtual gate points at cardinal directions
      const cityRadius = this.cityRadius || 100;
      gatePoints = [
        new Point(cityRadius, 0),           // East
        new Point(0, cityRadius),           // North
        new Point(-cityRadius, 0),          // West
        new Point(0, -cityRadius)           // South
      ];
      
      // Snap each virtual gate to nearest border vertex
      const snappedGates = [];
      for (const virtualGate of gatePoints) {
        let nearest = this.borderShape[0];
        let minDist = Point.distance(virtualGate, nearest);
        
        for (const borderVertex of this.borderShape) {
          const dist = Point.distance(virtualGate, borderVertex);
          if (dist < minDist) {
            minDist = dist;
            nearest = borderVertex;
          }
        }
        snappedGates.push(nearest);
      }
      gatePoints = snappedGates;
      // console.log('Created virtual gates:', gatePoints.length);
    }
    
    if (gatePoints.length === 0 || targetVertices.length === 0) {
      console.warn('Cannot build streets - gates:', gatePoints.length, 'targets:', targetVertices.length);
      return; // Can't build streets without gates or targets
    }
    
    // console.log('Building streets from', gatePoints.length, 'gates to', targetVertices.length, 'targets');
    
    // Find nearest target vertex for each gate
    for (const gate of gatePoints) {
      let nearestTarget = null;
      let minDist = Infinity;
      
      for (const vertex of targetVertices) {
        const dist = Point.distance(gate, vertex);
        if (dist < minDist) {
          minDist = dist;
          nearestTarget = vertex;
        }
      }
      
      if (nearestTarget) {
        const path = this.findPath(topology, gate, nearestTarget);
        if (path && path.length > 1) {
          this.streets.push(path);
          // console.log('Added street with', path.length, 'points');
        } else {
          console.warn('Failed to find path from gate to target');
        }
      }
    }
    
    // console.log('Total streets built:', this.streets.length);
    
    // Add exterior roads from gates
    this.exteriorRoads = [];
    
    // Use actual gates or virtual gates for exterior roads
    const roadStartPoints = gatePoints;
    
    // Get all exterior patches
    const exteriorPatches = this.patches.filter(p => p.ward && !p.withinCity);
    
    // Build extended topology that includes exterior vertices
    const extendedGraph = new Map(topology);
    
    // Add all exterior patch edges to the graph
    for (const patch of exteriorPatches) {
      for (let i = 0; i < patch.shape.length; i++) {
        const v0 = patch.shape[i];
        const v1 = patch.shape[(i + 1) % patch.shape.length];
        
        if (!extendedGraph.has(v0)) extendedGraph.set(v0, {edges: new Map()});
        if (!extendedGraph.has(v1)) extendedGraph.set(v1, {edges: new Map()});
        
        const dist = Point.distance(v0, v1);
        extendedGraph.get(v0).edges.set(v1, dist);
        extendedGraph.get(v1).edges.set(v0, dist);
      }
    }
    
    // For each gate (real or virtual), pathfind outward to a far point
    for (const gate of roadStartPoints) {
      const angle = Math.atan2(gate.y, gate.x);
      const roadLength = this.cityRadius * 1.5;
      
      // Find the farthest vertex in the extended graph along this direction
      let bestTarget = null;
      let maxDist = 0;
      
      for (const vertex of extendedGraph.keys()) {
        // Check if vertex is roughly in the gate's direction
        const dx = vertex.x - gate.x;
        const dy = vertex.y - gate.y;
        const vertexAngle = Math.atan2(dy, dx);
        const angleDiff = Math.abs(vertexAngle - angle);
        
        // Within 45 degrees of the gate direction
        if (angleDiff < Math.PI / 4 || angleDiff > (2 * Math.PI - Math.PI / 4)) {
          const dist = Math.sqrt(dx * dx + dy * dy);
          if (dist > maxDist) {
            maxDist = dist;
            bestTarget = vertex;
          }
        }
      }
      
      if (!bestTarget) {
        // Fallback: just use the farthest vertex from gate
        for (const vertex of extendedGraph.keys()) {
          const dist = Point.distance(gate, vertex);
          if (dist > maxDist) {
            maxDist = dist;
            bestTarget = vertex;
          }
        }
      }
      
      if (bestTarget) {
        // Find path using the extended graph
        let path = this.findPath(extendedGraph, gate, bestTarget);
        
        if (path && path.length > 1) {
          // Filter out any points that move back toward center (0,0)
          const filteredPath = [path[0]]; // Always include gate
          let maxDistSoFar = Math.sqrt(gate.x * gate.x + gate.y * gate.y);
          
          for (let i = 1; i < path.length; i++) {
            const point = path[i];
            const pointDist = Math.sqrt(point.x * point.x + point.y * point.y);
            
            // Only include points that maintain or increase distance from center
            if (pointDist >= maxDistSoFar - 5) { // Small tolerance
              filteredPath.push(point);
              maxDistSoFar = Math.max(maxDistSoFar, pointDist);
            }
          }
          
          if (filteredPath.length > 1) {
            this.exteriorRoads.push(filteredPath);
          }
        }
      }
    }
  }
  
  buildTopology() {
    // Build graph of all Voronoi vertices
    const graph = new Map(); // Point -> {edges: Map<Point, distance>}
    
    // Build graph from ALL patch edges - don't block anything initially
    for (const patch of this.patches) {
      for (let i = 0; i < patch.shape.length; i++) {
        const v0 = patch.shape[i];
        const v1 = patch.shape[(i + 1) % patch.shape.length];
        
        // Add vertices to graph
        if (!graph.has(v0)) graph.set(v0, {edges: new Map()});
        if (!graph.has(v1)) graph.set(v1, {edges: new Map()});
        
        // Check if this edge crosses the wall (but not at a gate)
        const isWallEdge = this.borderShape && (
          (this.borderShape.includes(v0) && this.borderShape.includes(v1))
        );
        
        const isGateEdge = this.gates.some(g => 
          (g.x === v0.x && g.y === v0.y) || (g.x === v1.x && g.y === v1.y)
        );
        
        // Skip edges that are wall segments (unless they involve a gate)
        if (isWallEdge && !isGateEdge) continue;
        
        // Link bidirectional
        const dist = Point.distance(v0, v1);
        graph.get(v0).edges.set(v1, dist);
        graph.get(v1).edges.set(v0, dist);
      }
    }
    
    return graph;
  }
  
  findPath(graph, start, end) {
    // Find closest graph vertices to start and end
    let closestStart = null;
    let closestEnd = null;
    let minStartDist = Infinity;
    let minEndDist = Infinity;
    
    for (const vertex of graph.keys()) {
      const startDist = Point.distance(vertex, start);
      if (startDist < minStartDist) {
        minStartDist = startDist;
        closestStart = vertex;
      }
      
      const endDist = Point.distance(vertex, end);
      if (endDist < minEndDist) {
        minEndDist = endDist;
        closestEnd = vertex;
      }
    }
    
    if (!closestStart || !closestEnd) {
      console.log('Could not find closest vertices in graph');
      return null;
    }
    
    // A* pathfinding
    const openSet = new Set([closestStart]);
    const cameFrom = new Map();
    const gScore = new Map();
    const fScore = new Map();
    
    gScore.set(closestStart, 0);
    fScore.set(closestStart, Point.distance(closestStart, closestEnd));
    
    let iterations = 0;
    const maxIterations = graph.size * 10; // Safety limit
    
    while (openSet.size > 0 && iterations < maxIterations) {
      iterations++;
      
      // Find node in openSet with lowest fScore
      let current = null;
      let lowestF = Infinity;
      for (const node of openSet) {
        const f = fScore.get(node) || Infinity;
        if (f < lowestF) {
          lowestF = f;
          current = node;
        }
      }
      
      if (current === closestEnd) {
        // Reconstruct path
        const path = [end]; // Use actual end point
        while (cameFrom.has(current)) {
          path.unshift(current);
          current = cameFrom.get(current);
        }
        path.unshift(start); // Use actual start point
        return path;
      }
      
      openSet.delete(current);
      
      if (!graph.has(current)) continue;
      
      const neighbors = graph.get(current).edges;
      
      for (const [neighbor, dist] of neighbors) {
        const currentG = gScore.has(current) ? gScore.get(current) : Infinity;
        const tentativeG = currentG + dist;
        const currentNeighborG = gScore.has(neighbor) ? gScore.get(neighbor) : Infinity;
        
        if (tentativeG < currentNeighborG) {
          cameFrom.set(neighbor, current);
          gScore.set(neighbor, tentativeG);
          fScore.set(neighbor, tentativeG + Point.distance(neighbor, closestEnd));
          openSet.add(neighbor);
        }
      }
    }
    
    if (iterations >= maxIterations) {
      console.warn('A* pathfinding exceeded max iterations');
    }
    
    return null; // No path found
  }

  createWards() {
    // Ward types similar to original - weighted array
    const wardTypes = [
      'craftsmen', 'craftsmen', 'merchant', 'craftsmen', 'craftsmen', 'cathedral',
      'craftsmen', 'craftsmen', 'craftsmen', 'craftsmen', 'craftsmen',
      'craftsmen', 'craftsmen', 'craftsmen', 'administration', 'craftsmen',
      'slum', 'craftsmen', 'slum', 'patriciate', 'market',
      'slum', 'craftsmen', 'craftsmen', 'craftsmen', 'slum',
      'craftsmen', 'craftsmen', 'craftsmen', 'military', 'slum',
      'craftsmen', 'park', 'patriciate', 'market', 'merchant'
    ];
    
    let typeIndex = 0;
    const innerPatches = this.patches.filter(p => p.withinCity && p !== this.plaza && p !== this.citadel);
    
    // Plaza if needed
    if (this.plaza) {
      this.plaza.ward = new Plaza(this, this.plaza);
    }
    
    // Castle on citadel if present
    if (this.citadel) {
      this.citadel.ward = new Castle(this, this.citadel);
    }
    
    for (const patch of innerPatches) {
      const wardType = wardTypes[typeIndex % wardTypes.length];
      typeIndex++;
      
      if (wardType === 'cathedral') {
        patch.ward = new Cathedral(this, patch);
      } else if (wardType === 'market') {
        patch.ward = new Market(this, patch);
      } else if (wardType === 'park') {
        patch.ward = new Park(this, patch);
      } else if (wardType === 'slum') {
        patch.ward = new Slum(this, patch);
      } else {
        // All other types use standard Ward with type label
        patch.ward = new Ward(this, patch, wardType);
      }
    }
    
    // Calculate city radius from inner patches
    this.cityRadius = 0;
    for (const patch of this.patches) {
      if (patch.withinCity) {
        for (const v of patch.shape) {
          const dist = Math.sqrt(v.x * v.x + v.y * v.y);
          this.cityRadius = Math.max(this.cityRadius, dist);
        }
      }
    }
    
    // Assign farms to outer patches with good compactness
    for (const patch of this.patches) {
      if (!patch.withinCity && !patch.ward) {
        const compactness = this.calculateCompactness(patch.shape);
        if (Random.chance(0.2) && compactness >= 0.7) {
          patch.ward = new Farm(this, patch);
        }
      }
    }
  }
  
  calculateCompactness(shape) {
    // Compactness = 4π * area / perimeter²
    // Perfect circle = 1, less compact shapes < 1
    let area = 0;
    let perimeter = 0;
    
    for (let i = 0; i < shape.length; i++) {
      const v0 = shape[i];
      const v1 = shape[(i + 1) % shape.length];
      
      // Shoelace formula for area
      area += v0.x * v1.y - v1.x * v0.y;
      
      // Perimeter
      const dx = v1.x - v0.x;
      const dy = v1.y - v0.y;
      perimeter += Math.sqrt(dx * dx + dy * dy);
    }
    
    area = Math.abs(area) / 2;
    return perimeter > 0 ? (4 * Math.PI * area) / (perimeter * perimeter) : 0;
  }

  buildGeometry() {
    for (const patch of this.patches) {
      if (patch.ward) {
        patch.ward.buildGeometry();
      }
    }
  }
}

// ============================================================================
// Rendering
// ============================================================================

class Palette {
  static paper = '#F3EDE2';
  static light = '#4A3D2C';
  static dark = '#2B2416';
  static roof = '#8B7355'; // Brown roof color
}

class CityRenderer {
  constructor(canvas, model) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.model = model;
    this.formalMap = null;
    this.globalTrees = null;
    this.flythroughCamera = new FlythroughCamera();
    
    // 3D rendering support
    this.meshCache3D = null;  // Cached 3D meshes {buildings: [], walls: [], streets: []}
    this.camera3D = null;      // Renderer3D.Camera instance
  }

  render() {
    // Use 3D view if enabled
    if (StateManager.view3D) {
      this.render3D();
    } else if (StateManager.flythroughActive && window.generator && window.generator.flythroughCamera) {
      // Use flythrough camera if active
      window.generator.flythroughCamera.renderFirstPerson();
    } else if (StateManager.useViewArchitecture) {
      this.renderWithViews();
    } else {
      this.renderClassic();
    }
  }
  
  /**
   * Modern rendering using view architecture
   */
  renderWithViews() {
    const ctx = this.ctx;
    const width = this.canvas.width;
    const height = this.canvas.height;
    
    ctx.fillStyle = Palette.paper;
    ctx.fillRect(0, 0, width, height);
    
    const margin = 40;
    const baseScale = Math.min(
      (width - margin * 2) / (this.model.cityRadius * 2),
      (height - margin * 2) / (this.model.cityRadius * 2)
    );
    
    const scale = baseScale * (StateManager.zoom || 1.0);
    this.scale = scale;
    
    ctx.save();
    ctx.translate(width / 2 + StateManager.cameraOffsetX, height / 2 + StateManager.cameraOffsetY);
    ctx.scale(scale, scale);
    
    // Prepare city data for FormalMap
    const cityData = this.prepareCityData();
    
    // Create or update FormalMap (recreate if settings changed)
    if (!this.formalMap || this.settingsChanged()) {
      console.log('[View Arch] Creating new FormalMap with gap:', cityData.settings.buildingGap);
      this.formalMap = new FormalMap(cityData, Palette);
      this.lastSettings = {
        streetWidth: StateManager.streetWidth,
        buildingGap: StateManager.buildingGap,
        wallThickness: StateManager.wallThickness
      };
    }
    
    // Draw using view architecture
    this.formalMap.draw(ctx, {
      showBuildings: StateManager.showBuildings,
      showFarms: StateManager.showBuildings,
      showRoads: StateManager.showStreets,
      showWalls: true,
      showMajorRoads: StateManager.showStreets,
      showMinorRoads: StateManager.showStreets,
      showTowers: true,
      showGates: true,
      showFocus: StateManager.showFocus || false,
      showCellOutlines: StateManager.showCellOutlines
    });
    
    // Draw trees if enabled (before labels so labels appear on top)
    if (StateManager.showTrees) {
      if (!this.globalTrees) {
        this.globalTrees = this.spawnGlobalTrees();
      }
      if (this.globalTrees && this.globalTrees.length > 0) {
        this.drawTrees(ctx, this.globalTrees);
      }
    }
    
    // Draw labels if enabled (after trees so they appear on top)
    if (StateManager.showLabels) {
      for (const patch of this.model.patches) {
        if (patch.ward) {
          this.drawLabel(ctx, patch, patch.ward.getLabel());
        } else if (patch === this.model.plaza) {
          this.drawLabel(ctx, patch, 'Plaza');
        } else if (patch === this.model.citadel && !patch.ward) {
          this.drawLabel(ctx, patch, 'Citadel');
        }
      }
    }
    
    ctx.restore();
  }
  
  /**
   * Prepare city data structure for view architecture
   */
  prepareCityData() {
    const wards = [];
    
    // Convert patches to ward data
    for (const patch of this.model.patches) {
      const wardData = {
        shape: patch.shape,
        color: this.getPatchColor(patch),
        type: this.getPatchType(patch),
        buildings: [],
        furrows: null
      };
      
      // Add buildings if ward has geometry
      if (patch.ward && patch.ward.geometry) {
        // Store original building shapes (don't apply gap here - PatchView will do it)
        wardData.buildings = patch.ward.geometry.map(building => ({
          shape: [...building.map(p => ({...p}))], // Deep copy to avoid mutations
          height: Random.float(8, 20),
          type: 'residential'
        }));
      }
      
      // Add farm furrows if farm
      if (patch.ward instanceof Farm) {
        wardData.furrows = patch.ward.furrows || [];
      }
      
      wards.push(wardData);
    }
    
    // Convert streets to road data
    const streets = this.model.streets.map(street => ({
      path: street,
      major: street.major || false
    }));
    
    // Add exterior roads
    if (this.model.exteriorRoads) {
      for (const road of this.model.exteriorRoads) {
        streets.push({
          path: road,
          major: false
        });
      }
    }
    
    // Convert walls to wall data
    const walls = [];
    if (this.model.wallsNeeded && this.model.borderShape && this.model.borderShape.length > 0) {
      walls.push({
        path: this.model.borderShape,
        towers: this.generateWallTowers(this.model.borderShape),
        gates: this.model.gates.map(gate => ({
          x: gate.x,
          y: gate.y,
          width: 8,
          height: 12,
          angle: Math.atan2(gate.y, gate.x)
        }))
      });
    }
    
    // Add citadel walls
    for (const patch of this.model.patches) {
      if (patch.ward instanceof Castle && patch.ward.wall) {
        walls.push({
          path: patch.ward.wall,
          towers: this.generateWallTowers(patch.ward.wall),
          gates: []
        });
      }
    }
    
    return {
      wards: wards,
      streets: streets,
      walls: walls,
      settings: {
        streetWidth: (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0,
        buildingGap: (StateManager.buildingGap !== undefined) ? StateManager.buildingGap : 1.8,
        wallThickness: (StateManager.wallThickness !== undefined) ? StateManager.wallThickness : 5
      }
    };
  }
  
  settingsChanged() {
    if (!this.lastSettings) return true;
    const changed = (
      this.lastSettings.streetWidth !== StateManager.streetWidth ||
      this.lastSettings.buildingGap !== StateManager.buildingGap ||
      this.lastSettings.wallThickness !== StateManager.wallThickness
    );
    if (changed) {
      console.log('[View Arch] Settings changed:', {
        old: this.lastSettings,
        new: {
          streetWidth: StateManager.streetWidth,
          buildingGap: StateManager.buildingGap,
          wallThickness: StateManager.wallThickness
        }
      });
    }
    return changed;
  }
  
  generateWallTowers(wallPath) {
    const towers = [];
    const spacing = 30;
    let distance = 0;
    
    for (let i = 0; i < wallPath.length - 1; i++) {
      const p1 = wallPath[i];
      const p2 = wallPath[i + 1];
      const segmentLength = Math.sqrt((p2.x - p1.x) ** 2 + (p2.y - p1.y) ** 2);
      
      let segmentDist = 0;
      while (segmentDist < segmentLength) {
        const t = segmentDist / segmentLength;
        towers.push({
          x: p1.x + (p2.x - p1.x) * t,
          y: p1.y + (p2.y - p1.y) * t,
          radius: 4,
          type: Random.chance(0.7) ? 'round' : 'square'
        });
        segmentDist += spacing;
      }
      
      distance += segmentLength;
    }
    
    return towers;
  }
  
  getPatchColor(patch) {
    if (patch === this.model.plaza || (patch.ward && patch.ward instanceof Plaza)) {
      return '#D4C5A0';
    } else if (patch === this.model.citadel) {
      return '#D5C8B8';
    } else if (patch.ward instanceof Farm) {
      const hue = 45 + Random.int(-10, 10);
      const sat = 25 + Random.int(-5, 5);
      const light = 85 + Random.int(-5, 5);
      return `hsl(${hue}, ${sat}%, ${light}%)`;
    } else if (patch.ward instanceof Park) {
      return '#C8D4A8';
    } else if (patch.ward instanceof Slum) {
      return '#B8B0A0';
    } else {
      return Palette.light;
    }
  }
  
  getPatchType(patch) {
    if (patch.ward instanceof Farm) return 'farm';
    if (patch.ward instanceof Park) return 'park';
    if (patch.ward instanceof Slum) return 'slum';
    if (patch.ward instanceof Castle) return 'castle';
    if (patch.ward instanceof Cathedral) return 'temple';
    if (patch.ward instanceof Market) return 'market';
    return 'residential';
  }

  /**
   * Classic rendering (original implementation)
   */
  renderClassic() {
    const ctx = this.ctx;
    const width = this.canvas.width;
    const height = this.canvas.height;
    
    ctx.fillStyle = Palette.paper;
    ctx.fillRect(0, 0, width, height);
    
    const margin = 40;
    const baseScale = Math.min(
      (width - margin * 2) / (this.model.cityRadius * 2),
      (height - margin * 2) / (this.model.cityRadius * 2)
    );
    
    // Top-down view transform (no flythrough code here)
    const scale = baseScale * (StateManager.zoom || 1.0);
    
    ctx.save();
    ctx.translate(width / 2 + StateManager.cameraOffsetX, height / 2 + StateManager.cameraOffsetY);
    ctx.scale(scale, scale);
    // City is centered at origin (0,0), no additional translation needed
    
    this.scale = scale;
    
    // Remove view mode filters - simplified
    for (const patch of this.model.patches) {
      this.drawPatch(ctx, patch);
    }
    
    if (this.model.wallsNeeded && this.model.borderShape && this.model.borderShape.length > 0) {
      this.drawWall(ctx, this.model.borderShape);
    }
    
    for (const street of this.model.streets) {
      this.drawStreet(ctx, street);
    }
    
    // Draw exterior roads
    if (this.model.exteriorRoads) {
      for (const road of this.model.exteriorRoads) {
        this.drawExteriorRoad(ctx, road);
      }
    }
    
    for (const patch of this.model.patches) {
      // Draw citadel walls for Castle wards
      if (patch.ward instanceof Castle) {
        this.drawCitadelWall(ctx, patch.ward);
      }
      
      // Draw ward geometry (buildings)
      if (patch.ward && patch.ward.geometry) {
        this.drawBuildings(ctx, patch.ward.geometry);
      }
    }
    
    for (const gate of this.model.gates) {
      this.drawGate(ctx, gate);
    }
    
    // Draw trees if enabled (before labels so labels appear on top)
    if (StateManager.showTrees) {
      // Global tree spawning across all patches
      if (!this.globalTrees) {
        this.globalTrees = this.spawnGlobalTrees();
      }
      if (this.globalTrees && this.globalTrees.length > 0) {
        this.drawTrees(ctx, this.globalTrees);
      }
    }
    
    // Draw ward labels if enabled (after trees so they appear on top)
    if (StateManager.showLabels) {
      for (const patch of this.model.patches) {
        if (patch.ward) {
          this.drawLabel(ctx, patch, patch.ward.getLabel());
        } else if (patch === this.model.plaza) {
          this.drawLabel(ctx, patch, 'Plaza');
        } else if (patch === this.model.citadel && !patch.ward) {
          this.drawLabel(ctx, patch, 'Citadel');
        }
      }
    }
    
    ctx.restore();
  }
  
  drawTrees(ctx, trees) {
    const outlineTrees = true; // Could make this a setting
    const strokeWidth = 0.3 / this.scale;
    
    // Draw outlines first if enabled
    if (outlineTrees) {
      ctx.strokeStyle = Palette.dark;
      ctx.lineWidth = strokeWidth * 2;
      
      for (const tree of trees) {
        ctx.save();
        ctx.translate(tree.pos.x, tree.pos.y);
        ctx.beginPath();
        ctx.moveTo(tree.crown[tree.crown.length - 1].x, tree.crown[tree.crown.length - 1].y);
        for (const point of tree.crown) {
          ctx.lineTo(point.x, point.y);
        }
        ctx.closePath();
        ctx.stroke();
        ctx.restore();
      }
    }
    
    // Draw filled tree crowns
    ctx.fillStyle = '#4A7C59'; // Dark green for trees
    
    for (const tree of trees) {
      ctx.save();
      ctx.translate(tree.pos.x, tree.pos.y);
      ctx.beginPath();
      ctx.moveTo(tree.crown[tree.crown.length - 1].x, tree.crown[tree.crown.length - 1].y);
      for (const point of tree.crown) {
        ctx.lineTo(point.x, point.y);
      }
      ctx.closePath();
      ctx.fill();
      ctx.restore();
    }
  }

  spawnGlobalTrees() {
    const trees = [];
    const cityRadius = this.model.cityRadius;
    
    // Base tree spacing and parameters
    const treeSpacing = 4.0; // Base spacing between trees
    const buildingDisplaceChance = 0.05; // 5% chance tree displaces a building
    const treePlacementMultiplier = 3.0; // Trees are 3x more likely to be placed than displace buildings
    
    // Save RNG state to avoid affecting deterministic generation
    const savedSeed = Random.seed;
    
    // Process each patch
    for (const patch of this.model.patches) {
      const ward = patch.ward;
      if (!ward || !patch.shape || patch.shape.length < 3) continue;
      
      // Calculate distance from city center to patch center
      const patchCenter = Polygon.centroid(patch.shape);
      const distanceFromCenter = Math.sqrt(patchCenter.x * patchCenter.x + patchCenter.y * patchCenter.y);
      const normalizedDistance = distanceFromCenter / cityRadius; // 0 (center) to 1+ (edge)
      
      // Linear density falloff from center to edge
      // At center: 1.0, at edge: 0.2, beyond edge: 0
      let densityMultiplier = Math.max(0, 1.0 - normalizedDistance * 0.8);
      
      // Special handling for different ward types
      let baseDensity = 0.4; // Default density
      let canPlaceTrees = true;
      
      if (ward instanceof Park) {
        baseDensity = 0.85; // Parks are very dense with trees
        densityMultiplier = 1.0; // Parks ignore distance falloff
      } else if (ward instanceof Farm) {
        // Farms have minimal trees - use deterministic check based on patch position
        baseDensity = 0.02; // Very sparse - only near farmhouse
        // Use patch center hash for deterministic placement
        const patchHash = ((patchCenter.x * 73856093) ^ (patchCenter.y * 19349663)) & 0x7FFFFFFF;
        canPlaceTrees = (patchHash % 100) < 30; // 30% of farms get trees (deterministic)
      } else if (ward instanceof Market || ward instanceof Cathedral) {
        baseDensity = 0.15; // Less trees in important civic areas
      } else if (ward instanceof Castle) {
        baseDensity = 0.1; // Minimal trees in military areas
      }
      
      if (!canPlaceTrees) continue;
      
      // Final density calculation
      const finalDensity = baseDensity * densityMultiplier;
      
      // Get available area for tree placement
      let availableArea = patch.shape;
      
      // For wards with buildings, potentially displace some buildings
      const wardTrees = [];
      
      // Fill area with Poisson-like sampling
      const points = this.fillAreaWithTreePattern(availableArea, treeSpacing, finalDensity);
      
      for (const point of points) {
        // Check if tree placement conflicts with building
        let canPlace = true;
        
        // Check against buildings in this ward
        if (ward.geometry) {
          for (const building of ward.geometry) {
            if (building.type === 'polygon' && this.isPointInPolygon(point, building.points)) {
              // Tree would be inside a building
              // Use deterministic hash for building displacement
              const pointHash = ((point.x * 73856093) ^ (point.y * 19349663)) & 0x7FFFFFFF;
              if ((pointHash % 100) >= buildingDisplaceChance * 100) {
                canPlace = false;
                break;
              }
              // Otherwise tree displaces building (rare)
            }
          }
        }
        
        // Apply tree placement probability (higher than building displacement)
        // Use deterministic hash for placement decision
        const pointHash2 = ((point.x * 19349663) ^ (point.y * 83492791)) & 0x7FFFFFFF;
        if (canPlace && (pointHash2 % 10000) < treePlacementMultiplier * finalDensity * 10000) {
          wardTrees.push({
            pos: point,
            crown: this.getTreeCrown()
          });
        }
      }
      
      trees.push(...wardTrees);
    }
    
    // Restore RNG state
    Random.seed = savedSeed;
    
    return trees;
  }

  fillAreaWithTreePattern(polygon, spacing, density) {
    const points = [];
    
    // Get bounding box
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const p of polygon) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x);
      maxY = Math.max(maxY, p.y);
    }
    
    // Grid-based sampling with jitter
    for (let y = minY; y < maxY; y += spacing) {
      for (let x = minX; x < maxX; x += spacing) {
        // Add jitter for more natural distribution
        const jitterX = (Random.float() - 0.5) * spacing * 0.8;
        const jitterY = (Random.float() - 0.5) * spacing * 0.8;
        const point = new Point(x + jitterX, y + jitterY);
        
        // Check if point is inside polygon
        if (this.isPointInPolygon(point, polygon)) {
          // Use Perlin noise for natural clustering
          const noiseValue = (PerlinNoise.noise(point.x * 0.05, point.y * 0.05) + 1) / 2;
          if (noiseValue < density) {
            points.push(point);
          }
        }
      }
    }
    
    return points;
  }

  getTreeCrown() {
    // Generate a random tree crown polygon (MFCG implementation)
    const r1 = Random.float();
    const r2 = Random.float();
    const r3 = Random.float();
    const gaussian = (r1 + r2 + r3) / 3 * 2 - 1;
    const radius = 1.5 * Math.pow(1.5, gaussian);
    
    const crown = [];
    for (let i = 0; i < 6; i++) {
      const angleOffset = (Random.float() + Random.float() + Random.float()) / 3;
      const angle = 2 * Math.PI * (i + angleOffset) / 6;
      
      const r4 = Random.float();
      const r5 = Random.float();
      const r6 = Random.float();
      const r7 = Random.float();
      const radiusVar = Math.abs((r4 + r5 + r6 + r7) / 2 - 1);
      const pointRadius = radius * (1 - 4/6 * radiusVar);
      
      crown.push(new Point(
        Math.cos(angle) * pointRadius,
        Math.sin(angle) * pointRadius
      ));
    }
    
    return crown;
  }

  isPointInPolygon(point, polygon) {
    // Ray casting algorithm
    let inside = false;
    for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
      const xi = polygon[i].x, yi = polygon[i].y;
      const xj = polygon[j].x, yj = polygon[j].y;
      
      const intersect = ((yi > point.y) !== (yj > point.y))
        && (point.x < (xj - xi) * (point.y - yi) / (yj - yi) + xi);
      if (intersect) inside = !inside;
    }
    return inside;
  }

  drawPatch(ctx, patch) {
    if (patch.shape.length === 0) return;
    
    ctx.beginPath();
    ctx.moveTo(patch.shape[0].x, patch.shape[0].y);
    for (let i = 1; i < patch.shape.length; i++) {
      ctx.lineTo(patch.shape[i].x, patch.shape[i].y);
    }
    ctx.closePath();
    
    // Fill based on type
    if (patch === this.model.plaza || (patch.ward && patch.ward instanceof Plaza)) {
      ctx.fillStyle = '#D4C5A0'; // More distinct tan/sand color for central plaza
    } else if (patch === this.model.citadel) {
      ctx.fillStyle = '#D5C8B8';
    } else if (patch.ward instanceof Farm) {
      // Different pale brown-green for each farm
      if (!patch.ward.farmColor) {
        const hue = 50 + Random.float() * 40; // Yellow-green to olive range
        const sat = 20 + Random.float() * 15; // Low saturation
        const light = 75 + Random.float() * 10; // Pale
        patch.ward.farmColor = `hsl(${hue}, ${sat}%, ${light}%)`;
      }
      ctx.fillStyle = patch.ward.farmColor;
    } else {
      ctx.fillStyle = '#FEFAF5';
    }
    ctx.fill();
    
    // Draw farm details AFTER fill, within cell bounds
    if (patch.ward instanceof Farm) {
      this.drawFarmDetails(ctx, patch.ward, patch.shape);
    }
    
    // Draw cell boundaries if option enabled
    if (StateManager.showCellOutlines) {
      ctx.strokeStyle = Palette.light + '30';
      ctx.lineWidth = 1 / this.scale;
      ctx.stroke();
    }
  }

  drawWall(ctx, wall) {
    if (wall.length === 0) return;
    
    const gates = this.model.gates || [];
    const wallThickness = (StateManager.wallThickness || 2) / this.scale;
    
    ctx.strokeStyle = Palette.dark;
    ctx.lineWidth = wallThickness;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    
    // Draw the complete wall
    ctx.beginPath();
    ctx.moveTo(wall[0].x, wall[0].y);
    for (let i = 1; i < wall.length; i++) {
      ctx.lineTo(wall[i].x, wall[i].y);
    }
    ctx.closePath();
    ctx.stroke();
    
    // Erase gaps at gates
    if (gates.length > 0) {
      ctx.save();
      ctx.globalCompositeOperation = 'destination-out';
      ctx.strokeStyle = 'black';
      ctx.lineWidth = wallThickness * 2;
      ctx.lineCap = 'round';
      
      for (const gate of gates) {
        ctx.beginPath();
        ctx.arc(gate.x, gate.y, wallThickness * 1.5, 0, Math.PI * 2);
        ctx.fill();
      }
      
      ctx.restore();
    }
  }

  drawCitadelWall(ctx, ward) {
    if (!ward.citadelWall) return;
    
    const wall = ward.citadelWall;
    const wallThickness = ((StateManager.wallThickness || 2) * 1.5) / this.scale;
    
    ctx.strokeStyle = Palette.dark;
    ctx.lineWidth = wallThickness;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    
    // Draw the citadel wall
    ctx.beginPath();
    ctx.moveTo(wall[0].x, wall[0].y);
    for (let i = 1; i < wall.length; i++) {
      ctx.lineTo(wall[i].x, wall[i].y);
    }
    ctx.closePath();
    ctx.stroke();
    
    // Erase gap at gate
    if (ward.citadelGate) {
      ctx.save();
      ctx.globalCompositeOperation = 'destination-out';
      ctx.strokeStyle = 'black';
      ctx.lineWidth = wallThickness * 2.5;
      ctx.lineCap = 'round';
      
      ctx.beginPath();
      ctx.arc(ward.citadelGate.x, ward.citadelGate.y, wallThickness * 2, 0, Math.PI * 2);
      ctx.fill();
      
      ctx.restore();
    }
  }

  drawStreet(ctx, street) {
    if (!StateManager.showStreets || street.length < 2) return;
    
    ctx.beginPath();
    ctx.moveTo(street[0].x, street[0].y);
    for (let i = 1; i < street.length; i++) {
      ctx.lineTo(street[i].x, street[i].y);
    }
    
    ctx.strokeStyle = Palette.light + '80';
    ctx.lineWidth = (StateManager.streetWidth || 2.0) / this.scale;
    ctx.stroke();
  }

  drawExteriorRoad(ctx, road) {
    if (!StateManager.showStreets || road.length < 2) return;
    
    ctx.beginPath();
    ctx.moveTo(road[0].x, road[0].y);
    for (let i = 1; i < road.length; i++) {
      ctx.lineTo(road[i].x, road[i].y);
    }
    
    // Thicker and more visible than interior streets
    ctx.strokeStyle = Palette.dark + '60';
    ctx.lineWidth = (StateManager.streetWidth * 1.5 || 3.0) / this.scale;
    ctx.lineCap = 'round';
    ctx.stroke();
  }

  drawBuildings(ctx, buildings) {
    if (!StateManager.showBuildings) return;
    
    const gap = this.model.buildingGap;
    
    // Process buildings with gap if needed
    let processedBuildings = buildings;
    if (gap > 0) {
      processedBuildings = buildings.map(building => {
        if (!Array.isArray(building) || building.length === 0) return building;
        
        const center = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
        center.x /= building.length;
        center.y /= building.length;
        const shrinkFactor = 1 - (gap * 0.15);
        return building.map(p => new Point(
          center.x + (p.x - center.x) * shrinkFactor,
          center.y + (p.y - center.y) * shrinkFactor
        ));
      }).filter(b => Array.isArray(b) && b.length > 0);
    } else {
      processedBuildings = buildings.filter(b => Array.isArray(b) && b.length > 0);
    }
    
    // Use BuildingPainter for 3D rendering
    BuildingPainter.paint(ctx, processedBuildings, Palette.roof, Palette.dark, 0.5, this.scale);
  }

  drawFarmDetails(ctx, farm, cellShape) {
    // Draw furrows within the cell bounds
    if (farm.furrows && farm.furrows.length > 0) {
      ctx.save();
      
      // Clip to cell shape
      ctx.beginPath();
      ctx.moveTo(cellShape[0].x, cellShape[0].y);
      for (let i = 1; i < cellShape.length; i++) {
        ctx.lineTo(cellShape[i].x, cellShape[i].y);
      }
      ctx.closePath();
      ctx.clip();
      
      // Draw furrows
      ctx.strokeStyle = Palette.dark + '40'; // Semi-transparent dark lines
      ctx.lineWidth = 0.3 / this.scale;
      
      for (const furrow of farm.furrows) {
        ctx.beginPath();
        ctx.moveTo(furrow.start.x, furrow.start.y);
        ctx.lineTo(furrow.end.x, furrow.end.y);
        ctx.stroke();
      }
      
      ctx.restore();
    }
  }

  drawGate(ctx, gate) {
    ctx.beginPath();
    ctx.arc(gate.x, gate.y, 2 / this.scale, 0, Math.PI * 2);
    ctx.fillStyle = Palette.light;
    ctx.fill();
  }

  drawLabel(ctx, patch, labelText) {
    if (!labelText) return;
    
    // Calculate center of patch
    let cx = 0, cy = 0;
    for (const p of patch.shape) {
      cx += p.x;
      cy += p.y;
    }
    cx /= patch.shape.length;
    cy /= patch.shape.length;
    
    ctx.save();
    const fontSize = 12 / this.scale; // Bigger font
    ctx.font = `bold ${fontSize}px sans-serif`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    
    // White border/background
    ctx.strokeStyle = '#FFFFFF';
    ctx.lineWidth = 4 / this.scale;
    ctx.lineJoin = 'round';
    ctx.strokeText(labelText, cx, cy);
    
    // Black text
    ctx.fillStyle = '#000000';
    ctx.fillText(labelText, cx, cy);
    ctx.restore();
  }


  

  getWardBuildingHeight(wardType) {
    const heights = {
      'castle': 800,
      'cathedral': 960,
      'temple': 896,
      'market': 384,
      'patriciate': 576,
      'merchants': 480,
      'craftsmen': 384,
      'residential': 384,
      'slum': 256,
      'farm': 192,
      'park': 0,
      'plaza': 0,
      'administration': 576  // Same as patriciate
    };
    return heights[wardType] || 6;
  }

  getWardColor3D(wardType) {
    const colors = {
      'castle': '#9B8D7B',
      'cathedral': '#4169E1',      // Royal blue
      'temple': '#9370DB',         // Medium purple
      'market': '#FFD700',         // Gold
      'patriciate': '#FF1493',     // Deep pink
      'merchants': '#00CED1',      // Dark turquoise
      'craftsmen': '#A89878',      // Original tan
      'residential': '#32CD32',    // Lime green
      'slum': '#696969',           // Dim gray
      'farm': '#D8C8A8',
      'park': '#C8D4A8',
      'plaza': '#D4C5A0',
      'administration': '#FF0000', // Bright red
      'military': '#8B0000'        // Dark red
    };
    return colors[wardType] || '#A89878';
  }

  calculatePolygonArea(polygon) {
    let area = 0;
    for (let i = 0; i < polygon.length; i++) {
      const j = (i + 1) % polygon.length;
      area += polygon[i].x * polygon[j].y;
      area -= polygon[j].x * polygon[i].y;
    }
    return Math.abs(area / 2);
  }

  shrinkPolygon(polygon, amount) {
    if (!polygon || polygon.length < 3 || amount <= 0) return polygon;
    
    // Calculate centroid
    let cx = 0, cy = 0;
    for (const p of polygon) {
      cx += p.x;
      cy += p.y;
    }
    cx /= polygon.length;
    cy /= polygon.length;
    
    // Shrink each vertex toward centroid
    const shrunk = [];
    for (const p of polygon) {
      const dx = p.x - cx;
      const dy = p.y - cy;
      const dist = Math.sqrt(dx * dx + dy * dy);
      
      if (dist < amount) {
        // Skip vertices too close to center
        continue;
      }
      
      const ratio = (dist - amount) / dist;
      shrunk.push(new Point(
        cx + dx * ratio,
        cy + dy * ratio
      ));
    }
    
    return shrunk.length >= 3 ? shrunk : polygon;
  }

  createRoadMesh(path, width, height) {
    if (!path || path.length < 2) return null;
    
    const vertices = [];
    const faces = [];
    const halfWidth = width / 2;
    
    // Create vertices along both sides of the path
    for (let i = 0; i < path.length; i++) {
      const p = path[i];
      
      // Calculate perpendicular direction
      let perpX, perpY;
      
      if (i === 0) {
        // First point: use direction to next point
        const dx = path[i + 1].x - p.x;
        const dy = path[i + 1].y - p.y;
        const len = Math.sqrt(dx * dx + dy * dy);
        perpX = -dy / len;
        perpY = dx / len;
      } else if (i === path.length - 1) {
        // Last point: use direction from previous point
        const dx = p.x - path[i - 1].x;
        const dy = p.y - path[i - 1].y;
        const len = Math.sqrt(dx * dx + dy * dy);
        perpX = -dy / len;
        perpY = dx / len;
      } else {
        // Middle points: average of incoming and outgoing directions
        const dx1 = p.x - path[i - 1].x;
        const dy1 = p.y - path[i - 1].y;
        const len1 = Math.sqrt(dx1 * dx1 + dy1 * dy1);
        const dx2 = path[i + 1].x - p.x;
        const dy2 = path[i + 1].y - p.y;
        const len2 = Math.sqrt(dx2 * dx2 + dy2 * dy2);
        
        const avgDx = (dx1 / len1 + dx2 / len2) / 2;
        const avgDy = (dy1 / len1 + dy2 / len2) / 2;
        const avgLen = Math.sqrt(avgDx * avgDx + avgDy * avgDy);
        perpX = -avgDy / avgLen;
        perpY = avgDx / avgLen;
      }
      
      // Create 4 vertices: left bottom, right bottom, left top, right top
      const leftX = p.x + perpX * halfWidth;
      const leftZ = p.y + perpY * halfWidth;
      const rightX = p.x - perpX * halfWidth;
      const rightZ = p.y - perpY * halfWidth;
      
      vertices.push(new window.Renderer3D.Vec3(leftX, 0, leftZ));           // Bottom left
      vertices.push(new window.Renderer3D.Vec3(rightX, 0, rightZ));         // Bottom right
      vertices.push(new window.Renderer3D.Vec3(leftX, height, leftZ));      // Top left
      vertices.push(new window.Renderer3D.Vec3(rightX, height, rightZ));    // Top right
    }
    
    // Create faces connecting segments
    for (let i = 0; i < path.length - 1; i++) {
      const baseIdx = i * 4;
      const nextIdx = (i + 1) * 4;
      
      // Top surface (2 triangles)
      faces.push([baseIdx + 2, nextIdx + 2, baseIdx + 3]);
      faces.push([nextIdx + 2, nextIdx + 3, baseIdx + 3]);
      
      // Bottom surface (2 triangles)
      faces.push([baseIdx, baseIdx + 1, nextIdx]);
      faces.push([nextIdx, baseIdx + 1, nextIdx + 1]);
      
      // Left side (2 triangles)
      faces.push([baseIdx, nextIdx, baseIdx + 2]);
      faces.push([nextIdx, nextIdx + 2, baseIdx + 2]);
      
      // Right side (2 triangles)
      faces.push([baseIdx + 1, baseIdx + 3, nextIdx + 1]);
      faces.push([nextIdx + 1, baseIdx + 3, nextIdx + 3]);
    }
    
    return { vertices, faces };
  }

  // Subdivide a path into smaller segments for better triangle resolution
  subdivideWallPath(path, maxSegmentLength = 10) {
    const subdivided = [];
    for (let i = 0; i < path.length; i++) {
      const p1 = path[i];
      const p2 = path[(i + 1) % path.length];
      subdivided.push(p1);
      
      const dx = p2.x - p1.x;
      const dy = p2.y - p1.y;
      const len = Math.sqrt(dx * dx + dy * dy);
      
      if (len > maxSegmentLength) {
        const numSegments = Math.ceil(len / maxSegmentLength);
        for (let j = 1; j < numSegments; j++) {
          const t = j / numSegments;
          subdivided.push({
            x: p1.x + dx * t,
            y: p1.y + dy * t
          });
        }
      }
    }
    return subdivided;
  }

  build3DMeshes() {
    // Invalidate cache if wall thickness or building gap changed
    const cacheKey = `${StateManager.wallThickness}_${StateManager.buildingGap}_${StateManager.buildingCount}`;
    if (this.meshCache3D && this.meshCache3DKey === cacheKey) {
      return this.meshCache3D;
    }

    if (!window.Renderer3D) {
      console.error('Renderer3D not loaded');
      return { buildings: [], walls: [], streets: [], ground: null };
    }

    const { Vec3, extrudePolygonToMesh } = window.Renderer3D;
    const buildings = [];
    const walls = [];
    const streets = [];
    
    // Create ground plane - 256x256 grid, 2x city radius (4x larger than previous 0.5x), scaled 64x
    const cityRadius = this.model.cityRadius || 100;
    const groundSize = cityRadius * 2 * 64;  // Scale 64x, 2x city radius
    const gridResolution = 256;  // 16x more triangles (was 64x64, now 256x256)
    const cellSize = (groundSize * 2) / gridResolution;
    
    const groundVertices = [];
    const groundFaces = [];
    
    // Create grid vertices
    for (let row = 0; row <= gridResolution; row++) {
      for (let col = 0; col <= gridResolution; col++) {
        const x = -groundSize + col * cellSize;
        const z = -groundSize + row * cellSize;
        groundVertices.push(new Vec3(x, 0, z));
      }
    }
    
    // Create grid faces (2 triangles per cell)
    for (let row = 0; row < gridResolution; row++) {
      for (let col = 0; col < gridResolution; col++) {
        const topLeft = row * (gridResolution + 1) + col;
        const topRight = topLeft + 1;
        const bottomLeft = (row + 1) * (gridResolution + 1) + col;
        const bottomRight = bottomLeft + 1;
        
        // Top face triangles
        groundFaces.push([topLeft, topRight, bottomLeft]);
        groundFaces.push([topRight, bottomRight, bottomLeft]);
        
        // Bottom face triangles (reverse winding)
        groundFaces.push([topLeft, bottomLeft, topRight]);
        groundFaces.push([topRight, bottomLeft, bottomRight]);
      }
    }
    
    const ground = {
      mesh: {
        vertices: groundVertices,
        faces: groundFaces
      },
      color: '#7A9B7A',
      type: 'ground'
    };

    for (const patch of this.model.patches) {
      if (!patch.ward || !patch.ward.geometry) continue;

      const wardType = patch.ward.wardType || 'residential';
      const buildingHeight = this.getWardBuildingHeight(wardType);

      // Group buildings by ward to reduce fragmentation
      const wardBuildings = [];
      for (const polygon of patch.ward.geometry) {
        if (!polygon || polygon.length < 3) continue;
        
        // Only create meshes for buildings larger than a minimum size
        const area = this.calculatePolygonArea(polygon);
        if (area < 10) continue; // Increased threshold to skip more tiny polygons
        
        // Debug farm buildings
        if (patch.ward instanceof Farm && wardBuildings.length === 0) {
          // console.log('Farm building polygon:', polygon);
          // console.log('Farm building area:', area);
        }
        
        // Apply building gap by shrinking polygon
        const buildingGap = StateManager.buildingGap || 0;
        let finalPolygon = polygon;
        
        if (buildingGap > 0) {
          // Shrink polygon inward by buildingGap
          finalPolygon = this.shrinkPolygon(polygon, buildingGap);
          if (!finalPolygon || finalPolygon.length < 3) continue;
        }
        
        const polygon2D = finalPolygon.map(p => ({ x: p.x * 64, y: p.y * 64 }));
        
        // Ensure the polygon is clean and valid before extrusion
        if (!window.extrudeBuildingMesh) {
          console.error('extrudeBuildingMesh not loaded');
          continue;
        }
        
        const mesh = window.extrudeBuildingMesh(polygon2D, buildingHeight);
        
        wardBuildings.push({
          mesh: mesh,
          color: this.getWardColor3D(wardType),
          wardType: wardType,
          height: buildingHeight
        });
      }
      
      // Add all ward buildings
      buildings.push(...wardBuildings);
    }

    if (this.model.borderShape && this.model.borderShape.length > 0) {
      const wallHeight = 960;
      const wallThickness = (StateManager.wallThickness || 5) * 64;
      const wallPath = this.subdivideWallPath(this.model.borderShape.map(p => ({x: p.x * 64, y: p.y * 64})), 960); // Subdivide into 120-unit segments
      const wallMesh = window.extrudeWallPath(wallPath, wallHeight, wallThickness);
      
      walls.push({
        mesh: wallMesh,
        color: '#8B7D6B',
        type: 'city-wall'
      });
    }

    for (const patch of this.model.patches) {
      if (patch.ward instanceof Castle && patch.ward.wall) {
        const wallHeight = 768;
        const wallThickness = (StateManager.wallThickness * 0.5 || 2.5) * 64;
        const wallPath = this.subdivideWallPath(patch.ward.wall.map(p => ({x: p.x * 64, y: p.y * 64})), 768); // Subdivide into 96-unit segments
        const wallMesh = window.extrudeWallPath(wallPath, wallHeight, wallThickness);
        
        walls.push({
          mesh: wallMesh,
          color: '#9B8D7B',
          type: 'citadel-wall'
        });
      }
    }

    // Build street meshes from this.streets (not this.model.streets)
    const cityStreets = this.streets || this.model.streets || [];
    // console.log(`Building 3D meshes - this.streets: ${this.streets ? this.streets.length : 'undefined'}`);
    // console.log(`Building 3D meshes - this.model.streets: ${this.model.streets ? this.model.streets.length : 'undefined'}`);
    // console.log(`Building 3D meshes for ${cityStreets.length} streets`);
    
    for (const street of cityStreets) {
      if (!street || street.length < 2) continue;
      
      // Streets are paths (arrays of points), not polygons
      // Create a ribbon/road mesh along the path
      const streetWidth = (StateManager.streetWidth || 4) * 64;
      const roadMesh = this.createRoadMesh(street.map(p => ({x: p.x * 64, y: p.y * 64})), streetWidth, 0.1);
      
      if (roadMesh && roadMesh.vertices.length > 0) {
        streets.push({
          mesh: roadMesh,
          color: '#888888',
          type: 'street'
        });
      }
    }
    
    // Also build exterior roads if they exist
    const cityRoads = this.exteriorRoads || this.model.exteriorRoads || [];
    // console.log(`Building 3D meshes - this.exteriorRoads: ${this.exteriorRoads ? this.exteriorRoads.length : 'undefined'}`);
    // console.log(`Building 3D meshes - this.model.exteriorRoads: ${this.model.exteriorRoads ? this.model.exteriorRoads.length : 'undefined'}`);
    // console.log(`Building 3D meshes for ${cityRoads.length} exterior roads`);
    
    for (const road of cityRoads) {
      if (!road || road.length < 2) continue;
      
      const roadWidth = (StateManager.streetWidth || 4) * 64;
      const roadMesh = this.createRoadMesh(road.map(p => ({x: p.x * 64, y: p.y * 64})), roadWidth, 0.1);
      
      if (roadMesh && roadMesh.vertices.length > 0) {
        streets.push({
          mesh: roadMesh,
          color: '#888888',
          type: 'road'
        });
      }
    }

    this.meshCache3D = { buildings, walls, streets, ground };
    this.meshCache3DKey = cacheKey;
    return this.meshCache3D;
  }

  render3D() {
    if (!window.Renderer3D) {
      console.error('Renderer3D not loaded');
      return;
    }

    const ctx = this.ctx;
    const width = this.canvas.width;
    const height = this.canvas.height;

    ctx.fillStyle = '#87CEEB';
    ctx.fillRect(0, 0, width, height);

    const { Camera, drawMesh } = window.Renderer3D;

    const scene = this.build3DMeshes();

    if (!this.camera3D) {
      this.camera3D = new Camera(
        StateManager.camera3DFOV,
        width / height,
        StateManager.camera3DNear,
        StateManager.camera3DFar
      );
    } else {
      this.camera3D.setPerspective(
        StateManager.camera3DFOV,
        width / height,
        StateManager.camera3DNear,
        StateManager.camera3DFar
      );
    }

    const cityRadius = this.model.cityRadius || 100;
    const cameraDistance = cityRadius * 1.2 * 64;  // Scale 64x
    const angle = StateManager.camera3DAngle;
    
    // Apply pan offset from 2D view (inverted to match 2D camera behavior)
    const panX = -StateManager.cameraOffsetX / StateManager.zoom * 64;  // Scale 64x
    const panZ = -StateManager.cameraOffsetY / StateManager.zoom * 64;  // Scale 64x
    
    const camX = Math.sin(angle) * cameraDistance + panX;
    const camY = StateManager.camera3DHeight;
    const camZ = Math.cos(angle) * cameraDistance + panZ;
    
    this.camera3D.setPosition(new window.Renderer3D.Vec3(camX, camY, camZ));
    this.camera3D.lookAt(new window.Renderer3D.Vec3(panX, 0, panZ));

    ctx.save();
    ctx.fillStyle = '#8B7355';
    ctx.fillRect(0, height, width, height);
    ctx.restore();

    const { drawContactShadows } = window.Renderer3D;

    // Collect ALL triangles from buildings, walls, and streets for unified depth sorting
    const allTriangles = [];

    // console.log(`3D Render - Streets enabled: ${StateManager.showStreets}, Street count: ${scene.streets.length}`);
    
    // RENDER GROUND FIRST (not depth sorted, always in back, no culling)
    if (scene.ground && scene.ground.mesh) {
      ctx.fillStyle = scene.ground.color;
      for (const face of scene.ground.mesh.faces) {
        const pa = scene.ground.mesh.vertices[face[0]];
        const pb = scene.ground.mesh.vertices[face[1]];
        const pc = scene.ground.mesh.vertices[face[2]];
        const ppa = this.camera3D.projectPoint(pa, width, height);
        const ppb = this.camera3D.projectPoint(pb, width, height);
        const ppc = this.camera3D.projectPoint(pc, width, height);
        
        // Skip triangles that are completely outside the view frustum
        if (!ppa.visible && !ppb.visible && !ppc.visible) continue;
        
        // Skip triangles completely behind the camera (but allow triangles that intersect near plane)
        if (ppa.viewZ > 0 && ppb.viewZ > 0 && ppc.viewZ > 0) continue;
        
        // Skip back-facing triangles (simple backface culling)
        const screenNormalZ = (ppb.x - ppa.x) * (ppc.y - ppa.y) - (ppb.y - ppa.y) * (ppc.x - ppa.x);
        if (screenNormalZ <= 0) continue;
        
        // Render ground immediately
        ctx.beginPath();
        ctx.moveTo(ppa.x, ppa.y);
        ctx.lineTo(ppb.x, ppb.y);
        ctx.lineTo(ppc.x, ppc.y);
        ctx.closePath();
        ctx.fill();
      }
    }

    if (StateManager.showStreets) {
      // console.log(`Processing ${scene.streets.length} streets for 3D rendering`);
      for (const street of scene.streets) {
        if (!street.mesh || !street.mesh.faces || street.mesh.faces.length === 0) {
          console.warn('Street has no mesh or faces:', street);
          continue;
        }
        
        for (const face of street.mesh.faces) {
          const pa = street.mesh.vertices[face[0]];
          const pb = street.mesh.vertices[face[1]];
          const pc = street.mesh.vertices[face[2]];
          
          if (!pa || !pb || !pc) {
            console.warn('Street face has missing vertices');
            continue;
          }
          
          const ppa = this.camera3D.projectPoint(pa, width, height);
          const ppb = this.camera3D.projectPoint(pb, width, height);
          const ppc = this.camera3D.projectPoint(pc, width, height);
          
          // Frustum culling - skip if completely outside view
          if (!ppa.visible && !ppb.visible && !ppc.visible) continue;
          
          // Skip triangles behind the camera (near-plane clipping)
          if (ppa.depth < -1 || ppb.depth < -1 || ppc.depth < -1) continue;
          
          // Backface culling
          const screenNormalZ = (ppb.x - ppa.x) * (ppc.y - ppa.y) - (ppb.y - ppa.y) * (ppc.x - ppa.x);
          if (screenNormalZ <= 0) continue;
          
          // Calculate face normal for lighting
          const v1 = pb.sub(pa);
          const v2 = pc.sub(pa);
          const normal = window.Renderer3D.Vec3.cross(v1, v2);
          normal.normalize();
          
          // Lighting
          const sunDir = new window.Renderer3D.Vec3(0.5, -0.7, 0.5);
          const sunDot = -window.Renderer3D.Vec3.dot(normal, sunDir);
          const ambient = 0.3;
          const diffuse = Math.max(0, sunDot);
          const brightness = Math.min(1.0, ambient + diffuse * 0.7);
          
          const avgDepth = ((ppa.depth || 0) + (ppb.depth || 0) + (ppc.depth || 0)) / 3;
          
          allTriangles.push({
            pa: ppa, pb: ppb, pc: ppc,
            depth: avgDepth,
            brightness: brightness,
            color: street.color,
            stroke: '#00000020'
          });
        }
      }
    }

    if (StateManager.showBuildings) {
      // Update slider max to actual building count
      const buildingCountSlider = document.getElementById('building-count');
      if (buildingCountSlider && parseInt(buildingCountSlider.max) !== scene.buildings.length) {
        buildingCountSlider.max = scene.buildings.length;
        buildingCountSlider.value = Math.min(StateManager.buildingCount, scene.buildings.length);
        document.getElementById('building-count-value').textContent = 
          buildingCountSlider.value === buildingCountSlider.max ? 'All' : buildingCountSlider.value;
      }
      
      // Limit buildings based on slider count
      const maxBuildings = Math.min(StateManager.buildingCount, scene.buildings.length);
      const visibleBuildings = scene.buildings.slice(0, maxBuildings);
      
      // console.log(`Rendering ${visibleBuildings.length} of ${scene.buildings.length} buildings`);
      
      for (let i = 0; i < visibleBuildings.length; i++) {
        const building = visibleBuildings[i];
        
        // if (i < 3) {
        //   console.log(`Building ${i}: ${building.mesh.vertices.length} vertices, ${building.mesh.faces.length} faces, color: ${building.color}`);
        // }
        
        // Project all triangles and add to global list
        for (const face of building.mesh.faces) {
          const pa = building.mesh.vertices[face[0]];
          const pb = building.mesh.vertices[face[1]];
          const pc = building.mesh.vertices[face[2]];
          const ppa = this.camera3D.projectPoint(pa, width, height);
          const ppb = this.camera3D.projectPoint(pb, width, height);
          const ppc = this.camera3D.projectPoint(pc, width, height);
          
          // Frustum culling - skip if completely outside view
          if (!ppa.visible && !ppb.visible && !ppc.visible) continue;
          
          // Skip triangles behind the camera (near-plane clipping)
          if (ppa.depth < -1 || ppb.depth < -1 || ppc.depth < -1) continue;
          
          // Backface culling
          const screenNormalZ = (ppb.x - ppa.x) * (ppc.y - ppa.y) - (ppb.y - ppa.y) * (ppc.x - ppa.x);
          if (screenNormalZ <= 0) continue;
          
          // Calculate face normal for lighting
          const v1 = pb.sub(pa);
          const v2 = pc.sub(pa);
          const normal = window.Renderer3D.Vec3.cross(v1, v2);
          normal.normalize();
          
          // Lighting
          const sunDir = new window.Renderer3D.Vec3(0.5, -0.7, 0.5);
          const sunDot = -window.Renderer3D.Vec3.dot(normal, sunDir);
          const ambient = 0.3;
          const diffuse = Math.max(0, sunDot);
          const brightness = Math.min(1.0, ambient + diffuse * 0.7);
          
          const avgDepth = ((ppa.depth || 0) + (ppb.depth || 0) + (ppc.depth || 0)) / 3;
          
          allTriangles.push({
            pa: ppa, pb: ppb, pc: ppc,
            depth: avgDepth,
            brightness: brightness,
            color: building.color,
            stroke: StateManager.showCellOutlines ? '#000000' : 'transparent',
            wardType: building.wardType,  // Track ward type for hover
            height: building.height
          });
        }
      }
    }

    if (StateManager.wallsNeeded) {
      for (const wall of scene.walls) {
        for (const face of wall.mesh.faces) {
          const pa = wall.mesh.vertices[face[0]];
          const pb = wall.mesh.vertices[face[1]];
          const pc = wall.mesh.vertices[face[2]];
          const ppa = this.camera3D.projectPoint(pa, width, height);
          const ppb = this.camera3D.projectPoint(pb, width, height);
          const ppc = this.camera3D.projectPoint(pc, width, height);
          
          // Frustum culling - skip if completely outside view
          if (!ppa.visible && !ppb.visible && !ppc.visible) continue;
          
          // Skip triangles with ANY vertex too close to camera (view-space Z clipping)
          if (ppa.viewZ > -RENDER_3D_CONFIG.NEAR_PLANE_CULL_THRESHOLD || 
              ppb.viewZ > -RENDER_3D_CONFIG.NEAR_PLANE_CULL_THRESHOLD || 
              ppc.viewZ > -RENDER_3D_CONFIG.NEAR_PLANE_CULL_THRESHOLD) continue;
          
          // Backface culling
          const screenNormalZ = (ppb.x - ppa.x) * (ppc.y - ppa.y) - (ppb.y - ppa.y) * (ppc.x - ppa.x);
          if (screenNormalZ <= 0) continue;
          
          // Calculate face normal for lighting
          const v1 = pb.sub(pa);
          const v2 = pc.sub(pa);
          const normal = window.Renderer3D.Vec3.cross(v1, v2);
          normal.normalize();
          
          // Lighting
          const sunDir = new window.Renderer3D.Vec3(0.5, -0.7, 0.5);
          const sunDot = -window.Renderer3D.Vec3.dot(normal, sunDir);
          const ambient = 0.3;
          const diffuse = Math.max(0, sunDot);
          const brightness = Math.min(1.0, ambient + diffuse * 0.7);
          
          const avgDepth = ((ppa.depth || 0) + (ppb.depth || 0) + (ppc.depth || 0)) / 3;
          
          allTriangles.push({
            pa: ppa, pb: ppb, pc: ppc,
            depth: avgDepth,
            brightness: brightness,
            color: wall.color,
            stroke: '#00000060'
          });
        }
      }
    }

    // Sort ALL triangles by depth (back to front) - ground already rendered separately
    allTriangles.sort((a, b) => b.depth - a.depth);
    
    // Draw all triangles in sorted order
    ctx.save();
    for (const tri of allTriangles) {
      if (!tri.pa.visible && !tri.pb.visible && !tri.pc.visible) continue;
      
      ctx.beginPath();
      ctx.moveTo(tri.pa.x, tri.pa.y);
      ctx.lineTo(tri.pb.x, tri.pb.y);
      ctx.lineTo(tri.pc.x, tri.pc.y);
      ctx.closePath();
      
      // Check if this triangle is hovered
      const isHovered = this.lastHoveredBuilding && tri === this.lastHoveredBuilding;
      
      // Shade color (or use yellow if hovered)
      let shadedColor;
      if (isHovered) {
        shadedColor = '#FFFF00'; // Bright yellow for hovered building
      } else {
        const hex = tri.color.replace('#', '');
        let r = parseInt(hex.substr(0, 2), 16);
        let g = parseInt(hex.substr(2, 2), 16);
        let b = parseInt(hex.substr(4, 2), 16);
        r = Math.floor(r * tri.brightness);
        g = Math.floor(g * tri.brightness);
        b = Math.floor(b * tri.brightness);
        shadedColor = '#' + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1);
      }
      
      ctx.fillStyle = shadedColor;
      ctx.fill();
      
      if (tri.stroke !== 'transparent' || isHovered) {
        ctx.strokeStyle = isHovered ? '#000000' : tri.stroke;
        ctx.lineWidth = isHovered ? 2 : 0.5;
        ctx.stroke();
      }
    }
    ctx.restore();
    
    // Store rendered triangles for hover detection
    this.lastRenderedTriangles = allTriangles;
    
    // Show ward name if hovering
    if (this.hoveredWardType) {
      this.showWardInfo(this.hoveredWardType);
    } else {
      this.hideWardInfo();
    }
  }

  showWardInfo(wardType) {
    let infoDiv = document.getElementById('ward-info');
    if (!infoDiv) {
      infoDiv = document.createElement('div');
      infoDiv.id = 'ward-info';
      infoDiv.style.position = 'fixed';
      infoDiv.style.top = '10px';
      infoDiv.style.right = '10px';
      infoDiv.style.background = 'rgba(0,0,0,0.8)';
      infoDiv.style.color = 'white';
      infoDiv.style.padding = '10px';
      infoDiv.style.borderRadius = '5px';
      infoDiv.style.fontSize = '14px';
      infoDiv.style.zIndex = '1000';
      infoDiv.style.pointerEvents = 'none';
      document.body.appendChild(infoDiv);
    }
    infoDiv.textContent = `Ward: ${wardType.charAt(0).toUpperCase() + wardType.slice(1)}`;
    infoDiv.style.display = 'block';
  }

  hideWardInfo() {
    const infoDiv = document.getElementById('ward-info');
    if (infoDiv) {
      infoDiv.style.display = 'none';
    }
  }


}

// ============================================================================
// Building and Farm Painters
// ============================================================================

class BuildingPainter {
  /**
   * Paint building polygons with roofs and walls
   * @param {CanvasRenderingContext2D} ctx - Canvas context
   * @param {Array<Array<Point>>} buildings - Array of building polygons
   * @param {string} roofColor - Color for roofs
   * @param {string} outlineColor - Color for outlines
   * @param {number} raised - Height factor for 3D effect (default 0.5)
   * @param {number} scale - Rendering scale
   */
  static paint(ctx, buildings, roofColor, outlineColor, raised = 0.5, scale = 1) {
    const strokeWidth = 0.5 / scale;
    let wallOffset = 0;
    
    // Draw 3D walls if raised
    if (raised > 0) {
      wallOffset = -1.2 * raised;
      const wallColor = Palette.dark;
      
      for (const building of buildings) {
        // Find vertical edges for wall drawing
        let wallSegment = null;
        
        for (let i = 0; i < building.length; i++) {
          const p0 = building[i];
          const p1 = building[(i + 1) % building.length];
          
          if (p1.x < p0.x) {
            // Start or continue wall segment
            if (!wallSegment) {
              wallSegment = [p0, p1];
            } else {
              wallSegment.push(p1);
            }
          } else if (wallSegment) {
            // End wall segment and draw it
            this.drawWallSegment(ctx, wallSegment, wallOffset, wallColor, outlineColor, strokeWidth);
            wallSegment = null;
          }
        }
        
        // Draw final segment if exists
        if (wallSegment) {
          this.drawWallSegment(ctx, wallSegment, wallOffset, wallColor, outlineColor, strokeWidth);
        }
      }
    }
    
    // Draw roofs with slight color variation
    for (const building of buildings) {
      // Add slight random variation to roof color
      const weathering = 0.1;
      const variance = (Random.float() + Random.float() + Random.float()) / 3 * 2 - 1;
      const variedRoof = this.scaleColor(roofColor, Math.pow(2, variance * weathering));
      
      ctx.fillStyle = variedRoof;
      ctx.strokeStyle = outlineColor;
      ctx.lineWidth = strokeWidth;
      
      ctx.beginPath();
      if (wallOffset !== 0) {
        // Draw roof at offset
        ctx.moveTo(building[0].x, building[0].y + wallOffset);
        for (let i = 1; i < building.length; i++) {
          ctx.lineTo(building[i].x, building[i].y + wallOffset);
        }
      } else {
        ctx.moveTo(building[0].x, building[0].y);
        for (let i = 1; i < building.length; i++) {
          ctx.lineTo(building[i].x, building[i].y);
        }
      }
      ctx.closePath();
      ctx.fill();
      ctx.stroke();
      
      // Draw roof details (simplified straight skeleton)
      this.drawRoofDetails(ctx, building, wallOffset, strokeWidth, outlineColor);
    }
  }
  
  static drawWallSegment(ctx, segment, offset, wallColor, outlineColor, strokeWidth) {
    // Create bottom edge of wall
    const bottom = segment.map(p => new Point(p.x, p.y - offset));
    bottom.reverse();
    
    // Draw wall face
    ctx.fillStyle = wallColor;
    ctx.strokeStyle = outlineColor;
    ctx.lineWidth = strokeWidth;
    
    ctx.beginPath();
    ctx.moveTo(segment[0].x, segment[0].y);
    for (let i = 1; i < segment.length; i++) {
      ctx.lineTo(segment[i].x, segment[i].y);
    }
    for (const p of bottom) {
      ctx.lineTo(p.x, p.y);
    }
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
    
    // Draw vertical edges if wall color differs from outline
    if (wallColor !== outlineColor) {
      ctx.strokeStyle = outlineColor;
      for (let i = 1; i < segment.length - 1; i++) {
        const p = segment[i];
        ctx.beginPath();
        ctx.moveTo(p.x, p.y);
        ctx.lineTo(p.x, p.y - offset);
        ctx.stroke();
      }
    }
  }
  
  static drawRoofDetails(ctx, building, offset, strokeWidth, color) {
    // Simplified roof detail - just draw towards center
    const center = {x: 0, y: 0};
    for (const p of building) {
      center.x += p.x;
      center.y += p.y;
    }
    center.x /= building.length;
    center.y /= building.length;
    
    ctx.strokeStyle = color;
    ctx.lineWidth = strokeWidth;
    
    // Draw lines from edges toward center for some edges
    for (let i = 0; i < building.length; i++) {
      if (Random.chance(0.3)) { // Only some edges
        const p = building[i];
        const dx = center.x - p.x;
        const dy = center.y - p.y;
        const len = Math.sqrt(dx * dx + dy * dy);
        
        if (len > 2) { // Only if not too close to center
          const ratio = 0.3;
          const endX = p.x + dx * ratio;
          const endY = p.y + dy * ratio + offset;
          
          ctx.beginPath();
          ctx.moveTo(p.x, p.y + offset);
          ctx.lineTo(endX, endY);
          ctx.stroke();
        }
      }
    }
  }
  
  static scaleColor(colorHex, factor) {
    // Parse hex color
    const hex = colorHex.replace('#', '');
    let r = parseInt(hex.substr(0, 2), 16);
    let g = parseInt(hex.substr(2, 2), 16);
    let b = parseInt(hex.substr(4, 2), 16);
    
    // Scale
    r = Math.min(255, Math.max(0, Math.floor(r * factor)));
    g = Math.min(255, Math.max(0, Math.floor(g * factor)));
    b = Math.min(255, Math.max(0, Math.floor(b * factor)));
    
    // Convert back to hex
    return '#' + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1);
  }




}

class FarmPainter {
  /**
   * Paint farm fields with furrows
   * @param {CanvasRenderingContext2D} ctx - Canvas context
   * @param {Object} farm - Farm object with subPlots and furrows
   * @param {number} scale - Rendering scale
   */
  static paint(ctx, farm, scale = 1) {
    const strokeWidth = 0.5 / scale;
    const greenColor = Palette.light;
    const darkColor = Palette.dark;
    
    // Draw field plots
    ctx.fillStyle = greenColor;
    ctx.strokeStyle = darkColor;
    ctx.lineWidth = strokeWidth;
    
    for (const plot of farm.subPlots || []) {
      ctx.beginPath();
      ctx.moveTo(plot[0].x, plot[0].y);
      for (let i = 1; i < plot.length; i++) {
        ctx.lineTo(plot[i].x, plot[i].y);
      }
      ctx.closePath();
      ctx.fill();
      ctx.stroke();
    }
    
    // Draw furrows (plowed lines)
    if (farm.furrows && farm.furrows.length > 0) {
      ctx.strokeStyle = darkColor;
      ctx.lineWidth = strokeWidth * 0.5;
      
      for (const furrow of farm.furrows) {
        ctx.beginPath();
        ctx.moveTo(furrow.start.x, furrow.start.y);
        ctx.lineTo(furrow.end.x, furrow.end.y);
        ctx.stroke();
      }
    }
    
    // Draw any farm buildings
    if (farm.buildings && farm.buildings.length > 0) {
      BuildingPainter.paint(ctx, farm.buildings, Palette.roof, darkColor, 0.3, scale);
    }
  }
}

class Namer {
  static prefixes = ['North', 'South', 'East', 'West', 'Old', 'New', 'Great', 'Little'];
  static roots = ['haven', 'ford', 'ton', 'bury', 'wick', 'ham', 'port', 'mouth', 'shire', 'field', 'wood', 'bridge'];
  static suffixes = ['gate', 'wall', 'keep', 'hold', 'watch', 'guard'];
  
  /**
   * Generate a simple medieval city name
   */
  static cityName() {
    if (Random.chance(0.3)) {
      // Prefix + root
      return Random.choice(this.prefixes) + Random.choice(this.roots);
    } else if (Random.chance(0.5)) {
      // Just root
      return this.capitalize(Random.choice(this.roots));
    } else {
      // Root + suffix
      return this.capitalize(Random.choice(this.roots)) + Random.choice(this.suffixes);
    }
  }
  
  /**
   * Generate district name based on type
   */
  static districtName(type, direction) {
    const types = {
      'castle': ['Castle', 'Citadel', 'Keep', 'Fortress'],
      'market': ['Market', 'Bazaar', 'Square', 'Plaza'],
      'temple': ['Temple', 'Cathedral', 'Church', 'Abbey'],
      'slum': ['Slums', 'Warrens', 'Alleys', 'Rookery'],
      'craft': ['Artisan', 'Craft', 'Trade', 'Guild'],
      'merchant': ['Merchant', 'Trade', 'Commerce', 'Exchange'],
      'park': ['Gardens', 'Park', 'Green', 'Grove']
    };
    
    const base = types[type] ? Random.choice(types[type]) : 'District';
    
    if (direction && Random.chance(0.5)) {
      return `${direction} ${base}`;
    }
    
    return base;
  }
  
  static capitalize(str) {
    return str.charAt(0).toUpperCase() + str.slice(1);
  }
}

// Add choice method to Random class
Random.choice = function(array) {
  return array[Random.int(0, array.length)];
};

// ============================================================================
// View Architecture (from MFCG)
// ============================================================================

/**
 * Focus - tracks a collection of faces (cells) and their boundaries
 * Used for highlighting/focusing on specific districts or ward groups
 */
class Focus {
  constructor(faces) {
    this.faces = faces || [];
    this.edges = [];
    this.vertices = [];
    this.bounds = null;
    
    if (this.faces.length > 0) {
      this.updateBounds();
    }
  }
  
  updateBounds() {
    // Build edges and vertices from faces
    const edgeSet = new Set();
    const vertexSet = new Set();
    
    for (const face of this.faces) {
      if (!face.shape) continue;
      
      const points = face.shape;
      for (let i = 0; i < points.length; i++) {
        const p1 = points[i];
        const p2 = points[(i + 1) % points.length];
        
        // Add edge (normalized to avoid duplicates)
        const edgeKey = `${Math.min(p1.x, p2.x)},${Math.min(p1.y, p2.y)}-${Math.max(p1.x, p2.x)},${Math.max(p1.y, p2.y)}`;
        edgeSet.add(edgeKey);
        
        // Add vertices
        vertexSet.add(`${p1.x},${p1.y}`);
      }
    }
    
    this.edges = Array.from(edgeSet);
    this.vertices = Array.from(vertexSet).map(v => {
      const [x, y] = v.split(',').map(Number);
      return new Point(x, y);
    });
    
    // Calculate bounding box
    if (this.vertices.length > 0) {
      const xs = this.vertices.map(v => v.x);
      const ys = this.vertices.map(v => v.y);
      this.bounds = {
        x: Math.min(...xs),
        y: Math.min(...ys),
        width: Math.max(...xs) - Math.min(...xs),
        height: Math.max(...ys) - Math.min(...ys)
      };
    }
  }
  
  contains(face) {
    return this.faces.includes(face);
  }
}

/**
 * FocusView - renders a visual highlight around focused districts
 */
class FocusView {
  constructor(focus, style = {}) {
    this.focus = focus;
    this.strokeStyle = style.strokeStyle || '#FF0000';
    this.lineWidth = style.lineWidth || 2;
    this.lineDash = style.lineDash || [5, 5];
  }
  
  draw(ctx) {
    if (!this.focus || this.focus.faces.length === 0) return;
    
    ctx.save();
    ctx.strokeStyle = this.strokeStyle;
    ctx.lineWidth = this.lineWidth;
    ctx.setLineDash(this.lineDash);
    
    // Draw outline around all faces in focus
    for (const face of this.focus.faces) {
      if (!face.shape) continue;
      
      ctx.beginPath();
      const points = face.shape;
      ctx.moveTo(points[0].x, points[0].y);
      for (let i = 1; i < points.length; i++) {
        ctx.lineTo(points[i].x, points[i].y);
      }
      ctx.closePath();
      ctx.stroke();
    }
    
    ctx.restore();
  }
}

/**
 * PatchView - renders individual patches (ward cells)
 * Handles fill colors, patterns, and details for each ward type
 */
class PatchView {
  constructor(patch, palette, settings) {
    this.patch = patch;
    this.palette = palette;
    this.settings = settings || { buildingGap: 1.8 };
  }
  
  draw(ctx, options = {}) {
    const patch = this.patch;
    if (!patch.shape || patch.shape.length < 3) return;
    
    const showBuildings = options.showBuildings !== false;
    const showFarms = options.showFarms !== false;
    const showCellOutlines = options.showCellOutlines || false;
    
    ctx.save();
    
    // Fill the patch with ward color
    ctx.fillStyle = patch.color || this.palette.light;
    ctx.strokeStyle = this.palette.dark;
    ctx.lineWidth = showCellOutlines ? 0.5 : 0;
    
    ctx.beginPath();
    ctx.moveTo(patch.shape[0].x, patch.shape[0].y);
    for (let i = 1; i < patch.shape.length; i++) {
      ctx.lineTo(patch.shape[i].x, patch.shape[i].y);
    }
    ctx.closePath();
    ctx.fill();
    if (showCellOutlines) ctx.stroke();
    
    // Draw buildings if this is a building ward
    if (showBuildings && patch.buildings && patch.buildings.length > 0) {
      const buildingShapes = patch.buildings.map(b => b.shape);
      
      // Apply building gap by shrinking polygons
      // IMPORTANT: Use !== undefined check because gap can be 0
      const gap = (this.settings.buildingGap !== undefined) ? this.settings.buildingGap : 1.8;
      console.log('[PatchView] Rendering buildings with gap:', gap, 'from settings:', this.settings.buildingGap, 'building count:', buildingShapes.length);
      let processedBuildings;
      if (gap > 0) {
        processedBuildings = buildingShapes.map(building => {
          if (!Array.isArray(building) || building.length === 0) return building;
          
          const center = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
          center.x /= building.length;
          center.y /= building.length;
          const shrinkFactor = 1 - (gap * 0.15);
          return building.map(p => new Point(
            center.x + (p.x - center.x) * shrinkFactor,
            center.y + (p.y - center.y) * shrinkFactor
          ));
        }).filter(b => Array.isArray(b) && b.length > 0);
      } else {
        // Even at gap=0, create new Point instances to avoid any reference issues
        processedBuildings = buildingShapes.map(building => 
          building.map(p => new Point(p.x, p.y))
        );
      }
      
      BuildingPainter.paint(ctx, processedBuildings, this.palette.roof, this.palette.dark, 0.5, 1);
    }
    
    // Draw farm details if this is a farm
    if (showFarms && patch.type === 'farm' && patch.furrows) {
      this.drawFarmDetails(ctx, patch);
    }
    
    ctx.restore();
  }
  
  drawFarmDetails(ctx, farm) {
    if (!farm.furrows || farm.furrows.length === 0) return;
    
    ctx.save();
    
    // Clip to cell boundary
    ctx.beginPath();
    ctx.moveTo(farm.shape[0].x, farm.shape[0].y);
    for (let i = 1; i < farm.shape.length; i++) {
      ctx.lineTo(farm.shape[i].x, farm.shape[i].y);
    }
    ctx.closePath();
    ctx.clip();
    
    // Draw furrows
    ctx.strokeStyle = 'rgba(101, 67, 33, 0.3)';
    ctx.lineWidth = 0.5;
    
    for (const furrow of farm.furrows) {
      // Safety check: ensure furrow has valid start and end points
      if (!furrow || furrow.length < 2 || !furrow[0] || !furrow[1]) continue;
      
      ctx.beginPath();
      ctx.moveTo(furrow[0].x, furrow[0].y);
      ctx.lineTo(furrow[1].x, furrow[1].y);
      ctx.stroke();
    }
    
    ctx.restore();
  }
}

/**
 * RoadsView - renders roads and streets with smoothing and styling
 */
class RoadsView {
  constructor(roads, palette, settings) {
    this.roads = roads || [];
    this.palette = palette;
    this.settings = settings || { streetWidth: 4.0 };
    this.smoothIterations = 2;
  }
  
  draw(ctx, options = {}) {
    const showMajor = options.showMajorRoads !== false;
    const showMinor = options.showMinorRoads !== false;
    
    ctx.save();
    
    // Draw in two passes: outline first, then fill
    if (showMajor) {
      this.drawRoadLayer(ctx, this.roads.filter(r => r.major), true);
    }
    if (showMinor) {
      this.drawRoadLayer(ctx, this.roads.filter(r => !r.major), false);
    }
    
    ctx.restore();
  }
  
  drawRoadLayer(ctx, roads, isMajor) {
    const baseWidth = this.settings.streetWidth || 4.0;
    const width = isMajor ? baseWidth * 0.75 : baseWidth * 0.375;
    const outlineWidth = isMajor ? baseWidth * 1.125 : baseWidth * 0.625;
    
    // Draw outlines
    ctx.strokeStyle = this.palette.dark;
    ctx.lineWidth = outlineWidth;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    
    for (const road of roads) {
      this.drawRoad(ctx, road);
    }
    
    // Draw fills
    ctx.strokeStyle = this.palette.paper;
    ctx.lineWidth = width;
    
    for (const road of roads) {
      this.drawRoad(ctx, road);
    }
  }
  
  drawRoad(ctx, road) {
    if (!road.path || road.path.length < 2) return;
    
    const smoothed = this.smoothRoad(road.path);
    
    ctx.beginPath();
    ctx.moveTo(smoothed[0].x, smoothed[0].y);
    for (let i = 1; i < smoothed.length; i++) {
      ctx.lineTo(smoothed[i].x, smoothed[i].y);
    }
    ctx.stroke();
  }
  
  smoothRoad(points) {
    if (points.length < 3) return points;
    
    let smoothed = [...points];
    
    // Apply Chaikin's corner cutting algorithm
    for (let iter = 0; iter < this.smoothIterations; iter++) {
      const newPoints = [];
      
      for (let i = 0; i < smoothed.length - 1; i++) {
        const p0 = smoothed[i];
        const p1 = smoothed[i + 1];
        
        // Cut corner: 25% from p0, 75% from p0
        const q = new Point(
          0.75 * p0.x + 0.25 * p1.x,
          0.75 * p0.y + 0.25 * p1.y
        );
        const r = new Point(
          0.25 * p0.x + 0.75 * p1.x,
          0.25 * p0.y + 0.75 * p1.y
        );
        
        if (i === 0) newPoints.push(p0);
        newPoints.push(q);
        newPoints.push(r);
        if (i === smoothed.length - 2) newPoints.push(p1);
      }
      
      smoothed = newPoints;
    }
    
    return smoothed;
  }
}

/**
 * WallsView - renders city walls, towers, and gates
 */
class WallsView {
  constructor(walls, palette, settings) {
    this.walls = walls || [];
    this.palette = palette;
    this.settings = settings || { wallThickness: 5 };
    this.towerSpacing = 30; // Distance between towers
    this.towerRadius = 4;
  }
  
  draw(ctx, options = {}) {
    if (this.walls.length === 0) return;
    
    const showTowers = options.showTowers !== false;
    const showGates = options.showGates !== false;
    
    ctx.save();
    
    // Draw wall segments
    ctx.strokeStyle = this.palette.dark;
    ctx.lineWidth = this.settings.wallThickness || 5;
    ctx.lineCap = 'square';
    ctx.lineJoin = 'miter';
    
    for (const wall of this.walls) {
      this.drawWallSegment(ctx, wall);
    }
    
    // Draw towers
    if (showTowers) {
      ctx.fillStyle = this.palette.dark;
      for (const wall of this.walls) {
        if (wall.towers) {
          for (const tower of wall.towers) {
            this.drawTower(ctx, tower);
          }
        }
      }
    }
    
    // Draw gates
    if (showGates) {
      ctx.fillStyle = this.palette.paper;
      ctx.strokeStyle = this.palette.dark;
      ctx.lineWidth = 2;
      
      for (const wall of this.walls) {
        if (wall.gates) {
          for (const gate of wall.gates) {
            this.drawGate(ctx, gate);
          }
        }
      }
    }
    
    ctx.restore();
  }
  
  drawWallSegment(ctx, wall) {
    if (!wall.path || wall.path.length < 2) return;
    
    ctx.beginPath();
    ctx.moveTo(wall.path[0].x, wall.path[0].y);
    for (let i = 1; i < wall.path.length; i++) {
      ctx.lineTo(wall.path[i].x, wall.path[i].y);
    }
    ctx.stroke();
  }
  
  drawTower(ctx, tower) {
    const radius = tower.radius || this.towerRadius;
    
    if (tower.type === 'square') {
      ctx.fillRect(
        tower.x - radius,
        tower.y - radius,
        radius * 2,
        radius * 2
      );
    } else {
      // Round tower (default)
      ctx.beginPath();
      ctx.arc(tower.x, tower.y, radius, 0, Math.PI * 2);
      ctx.fill();
    }
  }
  
  drawGate(ctx, gate) {
    const width = gate.width || 8;
    const height = gate.height || 12;
    
    ctx.save();
    ctx.translate(gate.x, gate.y);
    if (gate.angle) {
      ctx.rotate(gate.angle);
    }
    
    // Draw gate opening
    ctx.fillRect(-width / 2, -height / 2, width, height);
    ctx.strokeRect(-width / 2, -height / 2, width, height);
    
    // Draw gate arch
    ctx.beginPath();
    ctx.arc(0, -height / 2, width / 2, Math.PI, 0);
    ctx.fill();
    ctx.stroke();
    
    ctx.restore();
  }
}

/**
 * FormalMap - main container for all map views
 * Manages patches, roads, walls, and rendering order
 */
class FormalMap {
  constructor(city, palette) {
    this.city = city;
    this.palette = palette;
    this.settings = city.settings || {
      streetWidth: 4.0,
      buildingGap: 1.8,
      wallThickness: 5
    };
    this.patches = [];
    this.roads = null;
    this.walls = null;
    this.focus = null;
    this.focusView = null;
    
    this.initialize();
  }
  
  initialize() {
    // Create patch views for all wards
    if (this.city.wards) {
      for (const ward of this.city.wards) {
        this.patches.push(new PatchView(ward, this.palette, this.settings));
      }
    }
    
    // Create roads view
    if (this.city.streets) {
      this.roads = new RoadsView(this.city.streets, this.palette, this.settings);
    }
    
    // Create walls view
    if (this.city.walls) {
      this.walls = new WallsView(this.city.walls, this.palette, this.settings);
    }
  }
  
  setFocus(faces) {
    if (faces && faces.length > 0) {
      this.focus = new Focus(faces);
      this.focusView = new FocusView(this.focus);
    } else {
      this.focus = null;
      this.focusView = null;
    }
  }
  
  draw(ctx, options = {}) {
    ctx.save();
    
    // 1. Draw patches (wards with buildings/farms)
    for (const patch of this.patches) {
      patch.draw(ctx, options);
    }
    
    // 2. Draw roads
    if (this.roads && options.showRoads !== false) {
      this.roads.draw(ctx, options);
    }
    
    // 3. Draw walls
    if (this.walls && options.showWalls !== false) {
      this.walls.draw(ctx, options);
    }
    
    // 4. Draw focus overlay (if any)
    if (this.focusView && options.showFocus !== false) {
      this.focusView.draw(ctx);
    }
    
    ctx.restore();
  }
}

// ============================================================================
// Flythrough Camera System
// ============================================================================

class FlythroughCamera {
  constructor(cityModel, renderer) {
    this.model = cityModel;
    this.renderer = renderer;
    this.active = false;
    this.position = { x: 0, y: 0 };
    this.height = FLYTHROUGH_CONFIG.CAMERA_HEIGHT; // 6ft above ground
    this.angle = 0;
    this.speed = FLYTHROUGH_CONFIG.CAMERA_SPEED;
    this.path = [];
    this.pathIndex = 0;
    this.animationFrame = null;
  }
  
  start() {
    this.active = true;
    this.generatePath();
    // Reset position to start of path
    if (this.path.length > 0) {
      this.position = { x: this.path[0].x, y: this.path[0].y };
      this.pathIndex = 0;
    }
    this.animate();
  }
  
  stop() {
    this.active = false;
    if (this.animationFrame) {
      cancelAnimationFrame(this.animationFrame);
      this.animationFrame = null;
    }
  }
  
  generatePath() {
    // Find all street vertices within the city
    const streetPoints = [];
    
    for (const street of this.model.streets) {
      for (const point of street) {
        streetPoints.push({ x: point.x, y: point.y });
      }
    }
    
    // If no streets, create a circular path
    if (streetPoints.length === 0) {
      const radius = this.model.cityRadius * 0.8;
      const segments = 100;
      for (let i = 0; i < segments; i++) {
        const angle = (i / segments) * Math.PI * 2;
        streetPoints.push({
          x: Math.cos(angle) * radius,
          y: Math.sin(angle) * radius
        });
      }
    }
    
    // Create a smooth path through random street points
    this.path = [];
    const numPoints = Math.min(50, streetPoints.length);
    const visited = new Set();
    
    // Start from a random point
    let currentIdx = Random.int(0, streetPoints.length);
    
    for (let i = 0; i < numPoints; i++) {
      this.path.push(streetPoints[currentIdx]);
      visited.add(currentIdx);
      
      // Find nearest unvisited point
      let nearestIdx = -1;
      let nearestDist = Infinity;
      
      for (let j = 0; j < streetPoints.length; j++) {
        if (visited.has(j)) continue;
        
        const dx = streetPoints[j].x - streetPoints[currentIdx].x;
        const dy = streetPoints[j].y - streetPoints[currentIdx].y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        
        if (dist < nearestDist) {
          nearestDist = dist;
          nearestIdx = j;
        }
      }
      
      if (nearestIdx === -1) break;
      currentIdx = nearestIdx;
    }
    
    // Close the loop
    if (this.path.length > 0) {
      this.path.push(this.path[0]);
    }
    
    this.pathIndex = 0;
    this.position = this.path[0] || { x: 0, y: 0 };
  }
  
  update() {
    if (!this.active || this.path.length < 2) return;
    
    const current = this.path[this.pathIndex];
    const next = this.path[(this.pathIndex + 1) % this.path.length];
    
    // Move towards next point
    const dx = next.x - this.position.x;
    const dy = next.y - this.position.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    
    if (dist < this.speed) {
      // Reached waypoint, move to next
      this.pathIndex = (this.pathIndex + 1) % this.path.length;
      this.position = { x: next.x, y: next.y };
    } else {
      // Move towards waypoint
      this.position.x += (dx / dist) * this.speed;
      this.position.y += (dy / dist) * this.speed;
    }
    
    // Update angle to face movement direction (where we're going)
    this.angle = Math.atan2(dy, dx);
  }
  
  animate() {
    if (!this.active) return;
    
    this.update();
    
    // Trigger a render in the generator
    if (window.generator) {
      window.generator.render();
    }
    
    // Continue animation loop
    this.animationFrame = requestAnimationFrame(() => this.animate());
  }
  
  getTransform() {
    // Calculate first-person view position
    // Camera is offset slightly forward in the direction it's facing
    const lookAhead = FLYTHROUGH_CONFIG.LOOK_AHEAD_DISTANCE;
    const viewX = this.position.x + Math.cos(this.angle) * lookAhead;
    const viewY = this.position.y + Math.sin(this.angle) * lookAhead;
    
    return {
      x: this.position.x,      // Camera actual position
      y: this.position.y,
      viewX: viewX,            // Where camera is looking
      viewY: viewY,
      angle: this.angle,       // Direction camera is facing
      height: this.height,     // Height above ground (6ft)
      zoom: FLYTHROUGH_CONFIG.CAMERA_ZOOM // First-person zoom level
    };
  }
  
  /**
   * Render the city from this camera's first-person perspective
   */
  renderFirstPerson() {
    if (!this.active || !this.renderer) return;
    
    const ctx = this.renderer.ctx;
    const canvas = this.renderer.canvas;
    const width = canvas.width;
    const height = canvas.height;
    
    // Clear canvas
    ctx.fillStyle = Palette.paper;
    ctx.fillRect(0, 0, width, height);
    
    const margin = 40;
    const baseScale = Math.min(
      (width - margin * 2) / (this.model.cityRadius * 2),
      (height - margin * 2) / (this.model.cityRadius * 2)
    );
    
    // First-person camera transform
    const transform = this.getTransform();
    const scale = baseScale * transform.zoom;
    
    // Rotate canvas so the movement direction points up on screen
    // transform.angle is the direction of movement (from atan2(dy, dx))
    // We rotate by -angle + PI/2 so that the forward vector points "up" on screen
    const rotation = -transform.angle + Math.PI / 2;
    
    ctx.save();
    // Center on screen
    ctx.translate(width / 2, height / 2);
    // Rotate to face forward (movement direction = up on screen)
    ctx.rotate(rotation);
    // Apply zoom
    ctx.scale(scale, scale);
    // Translate to camera position (camera at 6ft height looking forward)
    ctx.translate(-transform.x, -transform.y);
    
    this.renderer.scale = scale;
    
    // Render city from first-person view
    for (const patch of this.model.patches) {
      this.renderer.drawPatch(ctx, patch);
    }
    
    if (this.model.wallsNeeded && this.model.borderShape && this.model.borderShape.length > 0) {
      this.renderer.drawWall(ctx, this.model.borderShape);
    }
    
    for (const street of this.model.streets) {
      this.renderer.drawStreet(ctx, street);
    }
    
    // Draw exterior roads
    if (this.model.exteriorRoads) {
      for (const road of this.model.exteriorRoads) {
        this.renderer.drawExteriorRoad(ctx, road);
      }
    }
    
    for (const patch of this.model.patches) {
      // Draw citadel walls for Castle wards
      if (patch.ward instanceof Castle) {
        this.renderer.drawCitadelWall(ctx, patch);
      }
    }
    
    if (StateManager.showLabels) {
      for (const patch of this.model.patches) {
        if (patch.ward instanceof Park) {
          this.renderer.drawLabel(ctx, patch, 'Park');
        } else if (patch === this.model.plaza) {
          this.renderer.drawLabel(ctx, patch, 'Plaza');
        } else if (patch === this.model.citadel && !patch.ward) {
          this.renderer.drawLabel(ctx, patch, 'Citadel');
        }
      }
    }
    
    // Draw trees if enabled
    if (StateManager.showTrees) {
      if (!this.renderer.globalTrees) {
        this.renderer.globalTrees = this.renderer.spawnGlobalTrees();
      }
      if (this.renderer.globalTrees && this.renderer.globalTrees.length > 0) {
        this.renderer.drawTrees(ctx, this.renderer.globalTrees);
      }
    }
    
    ctx.restore();
  }
}

// ============================================================================
// Application
// ============================================================================

class StateManager {
  static size = 15;
  static seed = -1;
  static plazaNeeded = true;
  static citadelNeeded = true;
  static wallsNeeded = true;
  static gridChaos = 0.4;
  static sizeChaos = 0.6;
  static cellChaos = 0.0;
  static alleyWidth = 0.6;
  static streetWidth = 4.0;
  static buildingGap = 1.8;
  static showLabels = false;
  static wallThickness = 5;
  static showCellOutlines = false;
  static showBuildings = true;
  static showStreets = true;
  static zoom = 1.0;
  static plazaChance = 0.3; // Chance of central feature in plaza
  static useViewArchitecture = false; // Toggle for view-based rendering
  static flythroughActive = false; // Flythrough camera mode
  static showTrees = false; // Render trees in parks
  static cameraOffsetX = 0; // Camera pan X offset
  static cameraOffsetY = 0; // Camera pan Y offset
  static view3D = false;     // Toggle between 2D and 3D rendering
  static camera3DHeight = 80; // 3D camera height for overview
  static camera3DFOV = 60;   // 3D camera field of view (degrees)
  static camera3DAngle = 0;  // 3D camera rotation angle (radians)
  static camera3DNear = 0.1; // 3D camera near clipping plane
  static camera3DFar = 4000; // 3D camera far clipping plane
  static buildingCount = 1000; // Number of buildings to render (1-1000)

  static pullParams() {
    const params = new URLSearchParams(window.location.search);
    
    const sizeParam = params.get('size');
    if (sizeParam) {
      const size = parseInt(sizeParam);
      if (!isNaN(size)) {
        StateManager.size = Math.max(6, Math.min(40, size));
      }
    }
    
    const seedParam = params.get('seed');
    if (seedParam) {
      const seed = parseInt(seedParam);
      if (!isNaN(seed) && seed > 0) {
        StateManager.seed = seed;
      }
    }
  }

  static pushParams() {
    if (StateManager.seed === -1) {
      Random.reset();
      StateManager.seed = Random.seed;
    }
    
    const url = new URL(window.location.href);
    url.searchParams.set('size', StateManager.size);
    url.searchParams.set('seed', StateManager.seed);
    
    window.history.replaceState(
      { size: StateManager.size, seed: StateManager.seed },
      '',
      url.toString()
    );
  }
}

class TownGenerator {
  constructor() {
    this.canvas = document.createElement('canvas');
    this.container = null;
    this.model = null;
    this.renderer = null;
    this.camera = null;
  }

  init(container) {
    this.container = container;
    
    // Only remove loading message, keep controls
    const loadingMsg = container.querySelector('.loading-message');
    if (loadingMsg) loadingMsg.remove();
    
    // Only add canvas if not already present
    if (!container.querySelector('canvas')) {
      container.appendChild(this.canvas);
    }
    
    this.resize();
    window.addEventListener('resize', () => this.resize());
    
    // Add mouse drag handlers for camera panning
    this.isDragging = false;
    this.dragStartX = 0;
    this.dragStartY = 0;
    this.dragStartOffsetX = 0;
    this.dragStartOffsetY = 0;
    
    this.canvas.addEventListener('mousedown', (e) => {
      this.isDragging = true;
      this.dragStartX = e.clientX;
      this.dragStartY = e.clientY;
      this.dragStartOffsetX = StateManager.cameraOffsetX;
      this.dragStartOffsetY = StateManager.cameraOffsetY;
      this.canvas.style.cursor = 'grabbing';
    });
    
    this.canvas.addEventListener('mousemove', (e) => {
      const rect = this.canvas.getBoundingClientRect();
      const scaleX = this.canvas.width / rect.width;
      const scaleY = this.canvas.height / rect.height;
      const mouseX = (e.clientX - rect.left) * scaleX;
      const mouseY = (e.clientY - rect.top) * scaleY;
      
      if (this.isDragging) {
        const dx = e.clientX - this.dragStartX;
        const dy = e.clientY - this.dragStartY;
        StateManager.cameraOffsetX = this.dragStartOffsetX + dx;
        StateManager.cameraOffsetY = this.dragStartOffsetY + dy;
        this.render();
        return;
      }
      
      // Check for hover in 3D view
      if (!StateManager.view3D || !this.lastRenderedTriangles) return;
      
      // Find the topmost triangle under the mouse
      let hoveredBuilding = null;
      for (let i = this.lastRenderedTriangles.length - 1; i >= 0; i--) {
        const tri = this.lastRenderedTriangles[i];
        if (!tri.wardType) continue;
        
        // Point-in-triangle test
        const pointInTriangle = (px, py, ax, ay, bx, by, cx, cy) => {
          const v0x = cx - ax, v0y = cy - ay;
          const v1x = bx - ax, v1y = by - ay;
          const v2x = px - ax, v2y = py - ay;
          const dot00 = v0x * v0x + v0y * v0y;
          const dot01 = v0x * v1x + v0y * v1y;
          const dot02 = v0x * v2x + v0y * v2y;
          const dot11 = v1x * v1x + v1y * v1y;
          const dot12 = v1x * v2x + v1y * v2y;
          const invDenom = 1 / (dot00 * dot11 - dot01 * dot01);
          const u = (dot11 * dot02 - dot01 * dot12) * invDenom;
          const v = (dot00 * dot12 - dot01 * dot02) * invDenom;
          return (u >= 0) && (v >= 0) && (u + v <= 1);
        };
        
        if (pointInTriangle(mouseX, mouseY, tri.pa.x, tri.pa.y, tri.pb.x, tri.pb.y, tri.pc.x, tri.pc.y)) {
          hoveredBuilding = tri;
          break;
        }
      }
      
      // If hover changed, store and re-render with yellow highlight
      if (hoveredBuilding !== this.lastHoveredBuilding) {
        this.lastHoveredBuilding = hoveredBuilding;
        this.hoveredWardType = hoveredBuilding ? hoveredBuilding.wardType : null;
        this.render();
      }
    });
    
    this.canvas.addEventListener('mouseup', () => {
      this.isDragging = false;
      this.canvas.style.cursor = 'grab';
    });
    
    this.canvas.addEventListener('mouseleave', () => {
      this.isDragging = false;
      this.canvas.style.cursor = 'grab';
    });
    
    // Add mouse wheel handler for zoom
    this.canvas.addEventListener('wheel', (e) => {
      e.preventDefault();
      
      // Scroll up (negative deltaY) = zoom in (increase zoom)
      // Scroll down (positive deltaY) = zoom out (decrease zoom)
      const zoomDelta = -e.deltaY * 0.001; // Scale factor for smooth zooming
      const newZoom = Math.max(0.1, Math.min(5.0, StateManager.zoom + zoomDelta));
      
      StateManager.zoom = newZoom;
      
      // Update zoom slider and display value
      const zoomSlider = document.getElementById('zoom-slider');
      const zoomValue = document.getElementById('zoom-value');
      if (zoomSlider && zoomValue) {
        zoomSlider.value = newZoom;
        zoomValue.textContent = newZoom.toFixed(1);
      }
      
      this.render();
    });
    
    this.canvas.style.cursor = 'grab';
    
    this.generate();
  }

  resize() {
    this.canvas.width = this.container.clientWidth;
    this.canvas.height = this.container.clientHeight;
    
    if (this.renderer) {
      this.renderer.render();
    }
  }

  generate() {
    CityModel.instance = null; // Clear old instance
    
    // Don't pull params on regenerate - use what's already set
    if (StateManager.seed === -1) {
      Random.reset();
      StateManager.seed = Random.seed;
    }
    
    StateManager.pushParams();
    
    let attempts = 0;
    while (!CityModel.instance && attempts < 10) {
      this.model = new CityModel(StateManager.size, StateManager.seed);
      attempts++;
    }
    
    if (!CityModel.instance) {
      console.error('Failed to generate city after 10 attempts');
      return;
    }
    
    this.model = CityModel.instance;
    this.renderer = new CityRenderer(this.canvas, this.model);
    // Create flythrough camera with renderer reference for first-person rendering
    this.flythroughCamera = new FlythroughCamera(this.model, this.renderer);
    // Clear cached trees when regenerating
    this.renderer.globalTrees = null;
    this.renderer.render();
    
    console.log('Generated city with seed:', StateManager.seed, 'size:', StateManager.size);
  }
  
  toggleFlythrough() {
    if (!this.flythroughCamera) {
      console.log('No flythrough camera available');
      return;
    }
    
    if (StateManager.flythroughActive) {
      console.log('Stopping flythrough');
      this.flythroughCamera.stop();
      StateManager.flythroughActive = false;
      this.render();
    } else {
      console.log('Starting flythrough - first person camera at 6ft height');
      StateManager.flythroughActive = true;
      this.flythroughCamera.start();
    }
  }

  render() {
    if (this.renderer) {
      this.renderer.render();
    }
    
    // Restart camera if flythrough is active but camera stopped
    if (StateManager.flythroughActive && this.camera && !this.camera.active) {
      console.log('Restarting stopped flythrough camera');
      this.camera.start();
    }
  }

  regenerate() {
    StateManager.seed = -1;
    this.generate();
  }
}

if (typeof window !== 'undefined') {
  window.TownGenerator = TownGenerator;
  window.StateManager = StateManager;
}

// Export for Node.js
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { TownGenerator, StateManager, CityModel, CityRenderer, Point, Random, MathUtils };
}
