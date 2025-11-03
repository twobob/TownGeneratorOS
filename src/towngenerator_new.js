/**
 * Medieval Fantasy City Generator - Pure JavaScript Implementation
 * No external dependencies - runs entirely in the browser
*  @author twobob @props Watabou 
*/

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

class Farm extends Ward {
  buildGeometry() {
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
      new Point(pos.x + cos * size - sin * size, pos.y + sin * size + cos * size),
      new Point(pos.x + cos * size + sin * size, pos.y + sin * size - cos * size),
      new Point(pos.x - cos * size + sin * size, pos.y - sin * size - cos * size),
      new Point(pos.x - cos * size - sin * size, pos.y - sin * size + cos * size)
    ];
    
    this.geometry = [housing];
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
    if (this.gates.length === 0 || !this.plaza) {
      return;
    }
    
    // Build topology graph for pathfinding
    const topology = this.buildTopology();
    
    // Find nearest plaza corner for each gate
    for (const gate of this.gates) {
      let nearestPlazaVertex = null;
      let minDist = Infinity;
      
      for (const vertex of this.plaza.shape) {
        const dist = Point.distance(gate, vertex);
        if (dist < minDist) {
          minDist = dist;
          nearestPlazaVertex = vertex;
        }
      }
      
      if (nearestPlazaVertex) {
        const path = this.findPath(topology, gate, nearestPlazaVertex);
        if (path && path.length > 1) {
          this.streets.push(path);
        }
      }
    }
    
    // Add exterior roads from gates - avoid farm patches
    this.exteriorRoads = [];
    for (const gate of this.gates) {
      // Calculate direction away from city center
      const angle = Math.atan2(gate.y, gate.x);
      const roadLength = this.cityRadius * 1.5;
      
      // Find farm patches along this direction to avoid
      const farmPatches = this.patches.filter(p => p.ward instanceof Farm);
      
      // Create slightly wiggly road that avoids farms
      const road = [gate];
      const segments = 10; // More segments for better farm avoidance
      let currentPoint = gate;
      
      for (let i = 1; i <= segments; i++) {
        const t = i / segments;
        const baseDist = roadLength * t;
        
        // Base direction
        let targetX = gate.x + Math.cos(angle) * baseDist;
        let targetY = gate.y + Math.sin(angle) * baseDist;
        
        // Check if target is inside any farm patch
        const targetPoint = new Point(targetX, targetY);
        let insideFarm = false;
        
        for (const farmPatch of farmPatches) {
          if (this.isPointInPolygon(targetPoint, farmPatch.shape)) {
            insideFarm = true;
            
            // Push road to edge of farm
            const farmCenter = farmPatch.shape.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
            farmCenter.x /= farmPatch.shape.length;
            farmCenter.y /= farmPatch.shape.length;
            
            // Direction away from farm center
            const awayAngle = Math.atan2(targetY - farmCenter.y, targetX - farmCenter.x);
            const pushDist = 15; // Push road 15 units away from farm
            
            targetX += Math.cos(awayAngle) * pushDist;
            targetY += Math.sin(awayAngle) * pushDist;
            break;
          }
        }
        
        // Add small wiggle if not avoiding farms
        if (!insideFarm && i > 1) {
          const wiggle = (Random.float() - 0.5) * 8;
          const perpAngle = angle + Math.PI / 2;
          targetX += Math.cos(perpAngle) * wiggle;
          targetY += Math.sin(perpAngle) * wiggle;
        }
        
        currentPoint = new Point(targetX, targetY);
        road.push(currentPoint);
      }
      
      this.exteriorRoads.push(road);
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
}

class CityRenderer {
  constructor(canvas, model) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.model = model;
  }

  render() {
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
    
    // Apply zoom factor
    const scale = baseScale * (StateManager.zoom || 1.0);
    
    this.scale = scale;
    
    ctx.save();
    ctx.translate(width / 2, height / 2);
    ctx.scale(scale, scale);
    
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
    
    // Draw ward labels if enabled
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
    
    for (const building of buildings) {
      // Buildings are now polygons, not rectangles
      if (Array.isArray(building) && building.length > 0) {
        let poly = building;
        
        // Shrink building by gap amount around its center
        if (gap > 0) {
          const center = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
          center.x /= building.length;
          center.y /= building.length;
          const shrinkFactor = 1 - (gap * 0.15);
          poly = building.map(p => new Point(
            center.x + (p.x - center.x) * shrinkFactor,
            center.y + (p.y - center.y) * shrinkFactor
          ));
        }
        
        ctx.beginPath();
        ctx.moveTo(poly[0].x, poly[0].y);
        for (let i = 1; i < poly.length; i++) {
          ctx.lineTo(poly[i].x, poly[i].y);
        }
        ctx.closePath();
        
        ctx.fillStyle = Palette.dark;
        ctx.fill();
        
        ctx.strokeStyle = Palette.light;
        ctx.lineWidth = 0.3 / this.scale;
        ctx.stroke();
      }
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
    this.renderer.render();
    
    console.log('Generated city with seed:', StateManager.seed, 'size:', StateManager.size);
  }

  render() {
    if (this.renderer) {
      this.renderer.render();
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
