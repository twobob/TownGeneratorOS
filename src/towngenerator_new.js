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

// Voronoi Diagram Configuration
const VORONOI_RELAXATION_ITERATIONS = 2;  // Number of Lloyd's relaxation iterations to apply to Voronoi diagram
                                           // Higher values create more uniform cell sizes (0-10 recommended)

// Chaikin Smoothing Configuration = TODO  this is not respected by the eliding algorithm yet
// Nor is it used in pathfinding et cetera
const CHAIKIN_SMOOTHING_ITERATIONS = 0;  // Number of Chaikin corner-cutting iterations for polygon smoothing
                                         // Higher values create smoother curves (0-4 recommended)

// Polygon Smoothing Configuration
const POLYGON_SMOOTHING_PASSES = 3;  // Default number of Laplacian smoothing passes for polygons
                                     // Used for coastlines, borders, and water bodies (0-10 recommended)

// Urquhart Graph Configuration
const APPLY_URQUHART_GRAPH = false;  // Apply Urquhart graph filtering to Delaunay triangulation
                                    // Removes longest edge from each triangle, creating a sparser graph

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

  length() {
    return Math.sqrt(this.x * this.x + this.y * this.y);
  }

  subtract(other) {
    return new Point(this.x - other.x, this.y - other.y);
  }

  static distance(p1, p2, caller = 'unknown') {
    if (!p1 || !p2 || p1.x === undefined || p1.y === undefined || p2.x === undefined || p2.y === undefined) {
      console.error(`[Point.distance] Invalid points from ${caller}:`, p1, p2);
      return Infinity;
    }
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

// Arc generation utility
class ArcGenerator {
  // Find circle passing through 3 points
  static getCircle(p0, v0, p1, v1) {
    // p0, p1 are points, v0, v1 are direction vectors from those points
    // Returns {c: centre, r: radius} or null
    const dx1 = v0.x, dy1 = v0.y;
    const dx2 = v1.x, dy2 = v1.y;
    
    const denom = dx1 * dy2 - dy1 * dx2;
    if (Math.abs(denom) < 0.0001) return null; // Parallel
    
    const dx = p1.x - p0.x;
    const dy = p1.y - p0.y;
    
    const t = (dx * dy2 - dy * dx2) / denom;
    
    const cx = p0.x + dx1 * t;
    const cy = p0.y + dy1 * t;
    const r = Math.sqrt((cx - p0.x) ** 2 + (cy - p0.y) ** 2);
    
    return {c: new Point(cx, cy), r: r};
  }
  
  // Generate arc points
  static getArc(circle, startAngle, endAngle, minSegmentLength) {
    if (!circle || circle.r < 0.001) return null;
    
    // Ensure we go the short way around
    let delta = endAngle - startAngle;
    if (delta > Math.PI) delta -= 2 * Math.PI;
    if (delta < -Math.PI) delta += 2 * Math.PI;
    
    const arcLength = Math.abs(delta * circle.r);
    const segments = Math.max(2, Math.ceil(arcLength / minSegmentLength));
    
    const points = [];
    for (let i = 0; i <= segments; i++) {
      const angle = startAngle + delta * i / segments;
      points.push(new Point(
        circle.c.x + circle.r * Math.cos(angle),
        circle.c.y + circle.r * Math.sin(angle)
      ));
    }
    
    return points;
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
    
    // Calculate circumcentre using perpendicular bisector intersection
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

  /**
   * Get the longest edge of this triangle
   * @returns {{a: Point, b: Point, length: number}} The longest edge with its endpoints and length
   */
  getLongestEdge() {
    const edge12 = Point.distance(this.p1, this.p2);
    const edge23 = Point.distance(this.p2, this.p3);
    const edge31 = Point.distance(this.p3, this.p1);
    
    if (edge12 >= edge23 && edge12 >= edge31) {
      return { a: this.p1, b: this.p2, length: edge12 };
    } else if (edge23 >= edge12 && edge23 >= edge31) {
      return { a: this.p2, b: this.p3, length: edge23 };
    } else {
      return { a: this.p3, b: this.p1, length: edge31 };
    }
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

  /**
   * Apply Urquhart graph filtering to the Delaunay triangulation
   * Marks the longest edge from each triangle for removal
   * Creates a sparser graph that approximates the relative neighborhood graph
   * Note: Edges are marked but triangulation is kept intact for Voronoi generation
   */
  applyUrquhartGraph() {
    // Collect all edges to mark as removed (longest edge from each triangle)
    const edgesToRemove = new Set();
    
    for (const triangle of this.triangles) {
      const longest = triangle.getLongestEdge();
      // Create a canonical edge key (smaller point first)
      const key = longest.a.x < longest.b.x || 
                  (longest.a.x === longest.b.x && longest.a.y < longest.b.y)
                  ? `${longest.a.x},${longest.a.y}-${longest.b.x},${longest.b.y}`
                  : `${longest.b.x},${longest.b.y}-${longest.a.x},${longest.a.y}`;
      edgesToRemove.add(key);
      
      // Mark the edge on the triangle for later filtering
      triangle.urquhartLongestEdge = longest;
    }
    
    // Store the removed edges for potential visualization or analysis
    this.urquhartRemovedEdges = Array.from(edgesToRemove);
    
    console.log('Urquhart graph: marked', edgesToRemove.size, 'longest edges from', this.triangles.length, 'triangles');
    
    return edgesToRemove;
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
    
    for (const tr of this.triangles) {
      if (tr.p1 === p || tr.p2 === p || tr.p3 === p) {
        r.vertices.push(tr);
      }
    }
    
    // Sort triangles by angle of their circumcentres around seed point
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
  // Calculate oriented bounding box (OBB) - returns 4 corners [p0, p1, p2, p3]
  static obb(polygon) {
    if (polygon.length < 3) return null;
    
    // Find convex hull first for better OBB
    const hull = Polygon.convexHull(polygon);
    
    let minArea = Infinity;
    let bestBox = null;
    
    // Try each edge of the hull as a potential OBB side
    for (let i = 0; i < hull.length; i++) {
      const p1 = hull[i];
      const p2 = hull[(i + 1) % hull.length];
      
      // Edge vector
      const dx = p2.x - p1.x;
      const dy = p2.y - p1.y;
      const len = Math.sqrt(dx * dx + dy * dy);
      if (len < 0.001) continue;
      
      // Normalized edge direction
      const ux = dx / len;
      const uy = dy / len;
      
      // Perpendicular direction
      const vx = -uy;
      const vy = ux;
      
      // Project all points onto both axes
      let minU = Infinity, maxU = -Infinity;
      let minV = Infinity, maxV = -Infinity;
      
      for (const p of polygon) {
        const u = (p.x - p1.x) * ux + (p.y - p1.y) * uy;
        const v = (p.x - p1.x) * vx + (p.y - p1.y) * vy;
        
        minU = Math.min(minU, u);
        maxU = Math.max(maxU, u);
        minV = Math.min(minV, v);
        maxV = Math.max(maxV, v);
      }
      
      const area = (maxU - minU) * (maxV - minV);
      
      if (area < minArea) {
        minArea = area;
        // Reconstruct box corners
        const corner = new Point(p1.x + minU * ux + minV * vx, p1.y + minU * uy + minV * vy);
        bestBox = [
          corner,
          new Point(corner.x + (maxU - minU) * ux, corner.y + (maxU - minU) * uy),
          new Point(corner.x + (maxU - minU) * ux + (maxV - minV) * vx, corner.y + (maxU - minU) * uy + (maxV - minV) * vy),
          new Point(corner.x + (maxV - minV) * vx, corner.y + (maxV - minV) * vy)
        ];
      }
    }
    
    return bestBox;
  }
  
  // Convex hull using Graham scan
  static convexHull(points) {
    if (points.length < 3) return points.slice();
    
    // Find bottom-most point (or leftmost if tie)
    let start = points[0];
    for (const p of points) {
      if (p.y < start.y || (p.y === start.y && p.x < start.x)) {
        start = p;
      }
    }
    
    // Sort by polar angle
    const sorted = points.slice().sort((a, b) => {
      if (a === start) return -1;
      if (b === start) return 1;
      
      const dx1 = a.x - start.x, dy1 = a.y - start.y;
      const dx2 = b.x - start.x, dy2 = b.y - start.y;
      
      const cross = dx1 * dy2 - dy1 * dx2;
      if (cross !== 0) return cross > 0 ? -1 : 1;
      
      // Collinear - closer point first
      return (dx1 * dx1 + dy1 * dy1) - (dx2 * dx2 + dy2 * dy2);
    });
    
    const hull = [sorted[0], sorted[1]];
    
    for (let i = 2; i < sorted.length; i++) {
      let top = hull[hull.length - 1];
      let nextTop = hull[hull.length - 2];
      
      while (hull.length > 1) {
        const dx1 = top.x - nextTop.x;
        const dy1 = top.y - nextTop.y;
        const dx2 = sorted[i].x - top.x;
        const dy2 = sorted[i].y - top.y;
        
        if (dx1 * dy2 - dy1 * dx2 > 0) break;
        
        hull.pop();
        top = hull[hull.length - 1];
        nextTop = hull[hull.length - 2];
      }
      
      hull.push(sorted[i]);
    }
    
    return hull;
  }
  
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
    const centre = polygon.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    centre.x /= polygon.length;
    centre.y /= polygon.length;
    return centre;
  }
  
  /**
   * Chaikin's corner-cutting algorithm for smooth curves
   * Creates a smooth curve by iteratively cutting corners
   * @param {Point[]} polygon - The polygon to smooth
   * @param {boolean} closed - Whether the polygon is closed
   * @param {number} iterations - Number of smoothing passes
   * @returns {Point[]} Smoothed polygon
   */
  static chaikin(polygon, closed = true, iterations = CHAIKIN_SMOOTHING_ITERATIONS) {
    if (!polygon || polygon.length < 2) return polygon;
    
    let result = polygon.slice();
    
    for (let iter = 0; iter < iterations; iter++) {
      const smoothed = [];
      const len = result.length;
      
      for (let i = 0; i < (closed ? len : len - 1); i++) {
        const p0 = result[i];
        const p1 = result[(i + 1) % len];
        
        // Cut corner: create two new points at 1/4 and 3/4 along the edge
        smoothed.push(new Point(
          p0.x * 0.75 + p1.x * 0.25,
          p0.y * 0.75 + p1.y * 0.25
        ));
        smoothed.push(new Point(
          p0.x * 0.25 + p1.x * 0.75,
          p0.y * 0.25 + p1.y * 0.75
        ));
      }
      
      // For open polylines, add the final point back
      if (!closed) {
        smoothed.push(result[len - 1]);
      }
      
      result = smoothed;
    }
    
    return result;
  }
  
  /**
   * Laplacian smoothing for closed polygons
  * Each vertex is averaged with its neighbours, except those in excludePoints
   * @param {Point[]} polygon - The polygon to smooth
   * @param {Point[]} excludePoints - Points to keep fixed (gates, etc)
   * @param {number} iterations - Number of smoothing passes
   * @returns {Point[]} Smoothed polygon
   */
  static smooth(polygon, excludePoints = null, iterations = 1) {
    if (!polygon || polygon.length < 3) return polygon;
    
    let result = polygon.slice();
    const len = result.length;
    
    for (let iter = 0; iter < iterations; iter++) {
      const smoothed = [];
      
      for (let i = 0; i < len; i++) {
        const curr = result[i];
        
        // Check if this point should be excluded from smoothing
        if (excludePoints && excludePoints.some(p => 
          Math.abs(p.x - curr.x) < 0.01 && Math.abs(p.y - curr.y) < 0.01
        )) {
          smoothed.push(curr);
        } else {
          // Average with neighbours
          const prev = result[(i + len - 1) % len];
          const next = result[(i + 1) % len];
          const avgX = (prev.x + next.x) / 2;
          const avgY = (prev.y + next.y) / 2;
          
          // Lerp between current and average (0.5 blend)
          smoothed.push(new Point(
            curr.x + (avgX - curr.x) * 0.5,
            curr.y + (avgY - curr.y) * 0.5
          ));
        }
      }
      
      result = smoothed;
    }
    
    return result;
  }
  
  /**
   * Laplacian smoothing for open polylines
   * @param {Point[]} polyline - The polyline to smooth
   * @param {Point[]} excludePoints - Points to keep fixed
   * @param {number} iterations - Number of smoothing passes
   * @returns {Point[]} Smoothed polyline
   */
  static smoothOpen(polyline, excludePoints = null, iterations = 1) {
    if (!polyline || polyline.length < 3) return polyline;
    
    let result = polyline.slice();
    const len = result.length;
    
    for (let iter = 0; iter < iterations; iter++) {
      const smoothed = [];
      
      for (let i = 0; i < len; i++) {
        const curr = result[i];
        
        // Always keep endpoints
        if (i === 0 || i === len - 1) {
          smoothed.push(curr);
          continue;
        }
        
        // Check if this point should be excluded from smoothing
        if (excludePoints && excludePoints.some(p => 
          Math.abs(p.x - curr.x) < 0.01 && Math.abs(p.y - curr.y) < 0.01
        )) {
          smoothed.push(curr);
        } else {
          // Average with neighbours
          const prev = result[i - 1];
          const next = result[i + 1];
          const avgX = (prev.x + next.x) / 2;
          const avgY = (prev.y + next.y) / 2;
          
          // Lerp between current and average
          smoothed.push(new Point(
            curr.x + (avgX - curr.x) * 0.5,
            curr.y + (avgY - curr.y) * 0.5
          ));
        }
      }
      
      result = smoothed;
    }
    
    return result;
  }
}

// ============================================================================
// DCEL (Doubly Connected Edge List) - lightweight topology for per-edge data

// Edge type flags to drive insetting around walls/roads/water
const EdgeType = {
  INNER: 0,
  WALL: 1,
  ROAD: 2,
  WATER: 3,
  BRIDGE: 4,
};

class DCELVertex {
  constructor(point) {
    this.p = point;         // Point
    this.halfEdge = null;   // One of outgoing half-edges
  }
}

class DCELHalfEdge {
  constructor() {
    this.origin = null; // DCELVertex
    this.twin = null;   // DCELHalfEdge
    this.next = null;   // DCELHalfEdge
    this.prev = null;   // DCELHalfEdge
    this.face = null;   // DCELFace
    this.data = EdgeType.INNER; // classification (WALL/ROAD/WATER/INNER)
  }

  midpoint() {
    const a = this.origin.p;
    const b = this.next ? this.next.origin.p : a;
    return new Point((a.x + b.x) * 0.5, (a.y + b.y) * 0.5);
  }

  asSegment() {
    const a = this.origin.p;
    const b = this.next ? this.next.origin.p : a;
    return [a, b];
  }
}

class DCELFace {
  constructor(id) {
    this.id = id;
    this.edge = null;  // one half-edge on the boundary
    this.patch = null; // back reference to Patch
  }

  // Iterate boundary half-edges once (assumes simple polygon)
  edges() {
    const result = [];
    if (!this.edge) return result;
    let e = this.edge;
    const start = e;
    do {
      result.push(e);
      e = e.next;
    } while (e && e !== start);
    return result;
  }

  // Return ordered vertices aligned to edges
  loop() {
    return this.edges().map(e => ({ v: e.origin.p, e }));
  }
}

// Geometry helpers for intersections
function segmentIntersectsSegment(a, b, c, d) {
  const o = (p, q, r) => (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x);
  const onSeg = (p, q, r) => Math.min(p.x, r.x) - 1e-6 <= q.x && q.x <= Math.max(p.x, r.x) + 1e-6 &&
                              Math.min(p.y, r.y) - 1e-6 <= q.y && q.y <= Math.max(p.y, r.y) + 1e-6;
  const o1 = o(a, b, c), o2 = o(a, b, d), o3 = o(c, d, a), o4 = o(c, d, b);
  if (((o1 > 0 && o2 < 0) || (o1 < 0 && o2 > 0)) && ((o3 > 0 && o4 < 0) || (o3 < 0 && o4 > 0))) return true;
  if (Math.abs(o1) < 1e-6 && onSeg(a, c, b)) return true;
  if (Math.abs(o2) < 1e-6 && onSeg(a, d, b)) return true;
  if (Math.abs(o3) < 1e-6 && onSeg(c, a, d)) return true;
  if (Math.abs(o4) < 1e-6 && onSeg(c, b, d)) return true;
  return false;
}

function segmentIntersectsPolygon(a, b, poly) {
  for (let i = 0; i < poly.length; i++) {
    const c = poly[i];
    const d = poly[(i + 1) % poly.length];
    if (segmentIntersectsSegment(a, b, c, d)) return true;
  }
  return false;
}

// ============================================================================
// City Generation
// ============================================================================

class Patch {
  constructor(shape) {
    this.shape = shape;
    this.withinCity = false;
    this.withinWalls = false;
    this.waterbody = false;  // New property for water features
    this.ward = null;
    this.face = null;        // DCELFace reference (built after Voronoi)
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

  /**
   * Calculate available building area, insetting from walls and water
   */
  getAvailable() {
    const shape = this.patch.shape;
    const n = shape.length;

    const streetWidth = (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0;
    const wallThickness = (StateManager.wallThickness !== undefined) ? StateManager.wallThickness : 5.0;
    const buildingGap = (StateManager.buildingGap !== undefined) ? StateManager.buildingGap : 1.8;

    // If we have a DCEL face, compute exact per-edge insets from edge types
    if (this.patch.face && this.patch.face.edge) {
      const loop = this.patch.face.loop();
      const edgeInsets = new Array(loop.length);
      const vertexRadii = new Array(loop.length).fill(0);

      for (let i = 0; i < loop.length; i++) {
        const e = loop[i].e;
        let inset = Math.max(0.6, buildingGap * 0.5);
        if (e.data === EdgeType.WALL) {
          inset = Math.max(inset, wallThickness / 2 + 1.2);
        } else if (e.data === EdgeType.ROAD || e.data === EdgeType.BRIDGE) {
          inset = Math.max(inset, streetWidth / 2 + buildingGap);
        } else if (e.data === EdgeType.WATER) {
          inset = Math.max(inset, wallThickness + 1.2);
        }
        edgeInsets[i] = inset;
      }

      // Vertex radii: round off tower corners where both incident edges are walls
      for (let i = 0; i < loop.length; i++) {
        const prevE = loop[(i + loop.length - 1) % loop.length].e;
        const currE = loop[i].e;
        let r = 0;
        if (prevE.data === EdgeType.WALL && currE.data === EdgeType.WALL) {
          r = Math.max(r, wallThickness / 2 + 1.2);
        }
        // Slight rounding near a gate point
        if (Array.isArray(this.model.gates)) {
          const v = loop[i].v;
          for (const g of this.model.gates) {
            if (Point.distance(v, g) < wallThickness) { r = Math.max(r, wallThickness * 0.4); break; }
          }
        }
        vertexRadii[i] = r;
      }

      let insetShape = this.insetWithVertexRadii(loop.map(x => x.v), edgeInsets, vertexRadii);
      // Hard constrain to interior of city walls 
      if (Array.isArray(this.model.borderShape) && this.model.borderShape.length >= 3) {
        insetShape = this.clipInside(insetShape, this.model.borderShape);
      }
      // Subtract water polygons from available area so no geometry is placed over water
      if (Array.isArray(this.model.waterBodies) && this.model.waterBodies.length > 0) {
        const beforeClip = insetShape.length;
        for (const water of this.model.waterBodies) {
          if (water && water.length >= 3) {
            const before = insetShape.length;
            insetShape = this.clipOutside(insetShape, water);
            if (insetShape.length !== before) {
              // Debug (suppressed): water clipped ward shape from before to insetShape.length
            }
          }
        }
      }
      return insetShape;
    }

    // Fallback to legacy heuristic if DCEL is not available
    const vertexRadii = new Array(n).fill(0);
    const edgeInsets = new Array(n).fill(Math.max(0.6, buildingGap * 0.5));

    for (let i = 0; i < n; i++) {
      const a = shape[i];
      const b = shape[(i + 1) % n];
      let isWall = false;
      if (this.model.wallEdges) {
        for (const [w1, w2] of this.model.wallEdges) {
          const m1 = (Point.distance(a, w1) < 0.1 && Point.distance(b, w2) < 0.1);
          const m2 = (Point.distance(a, w2) < 0.1 && Point.distance(b, w1) < 0.1);
          if (m1 || m2) { isWall = true; break; }
        }
      }
      if (isWall) edgeInsets[i] = Math.max(edgeInsets[i], wallThickness / 2 + 1.2);
    }

    let result = this.insetWithVertexRadii(shape, edgeInsets, vertexRadii);
    if (Array.isArray(this.model.borderShape) && this.model.borderShape.length >= 3) {
      result = this.clipInside(result, this.model.borderShape);
    }
    if (Array.isArray(this.model.waterBodies) && this.model.waterBodies.length > 0) {
      // Debug (suppressed): fallback path clipping against water bodies
      for (const water of this.model.waterBodies) {
        if (water && water.length >= 3) {
          const before = result.length;
          result = this.clipOutside(result, water);
          if (result.length !== before) {
            // Debug (suppressed): water clipped fallback ward from before to result.length
          }
        }
      }
    }
    return result;
  }
  
  /**
   * Inset polygon with vertex radii handling
   * @param {Array} polygon - The polygon vertices
   * @param {Array} edgeInsets - Inset distance for each edge
   * @param {Array} vertexRadii - Radius for circular cutout at each vertex
   */
  insetWithVertexRadii(polygon, edgeInsets, vertexRadii) {
    // Step 1: Basic edge-based inset using simpleInset algorithm
    let result = this.insetPolygon(polygon, edgeInsets);
    
    if (!result || result.length < 3) {
      return null;
    }
    
    // Step 2: Cut out circles at vertices where radius exceeds adjacent edge insets
    const n = polygon.length;
    for (let i = 0; i < n; i++) {
      const radius = vertexRadii[i];
      const prevEdgeInset = edgeInsets[(i + n - 1) % n];
      const currEdgeInset = edgeInsets[i];
      
      // Only cut out circle if vertex radius exceeds BOTH adjacent edge insets
      if (radius > prevEdgeInset && radius > currEdgeInset) {
        const vertex = polygon[i];
        
        // Create circle approximation (9-sided polygon)

        const circle = this.createRegularPolygon(9, radius, vertex);
        
        // Subtract circle from result (boolean AND with inverted circle)
        const cutResult = this.subtractPolygon(result, circle);
        
        if (cutResult && cutResult.length >= 3) {
          result = cutResult;
        }
      }
    }
    
    return result;
  }
  
  /**
   * Basic edge-based polygon insetting

   */
  insetPolygon(polygon, edgeInsets) {
    const n = polygon.length;
    if (n < 3) return polygon.slice();

    // Determine polygon orientation (positive = CCW)
    let area2 = 0;
    for (let i = 0; i < n; i++) {
      const a = polygon[i];
      const b = polygon[(i + 1) % n];
      area2 += a.x * b.y - b.x * a.y;
    }
    const ccw = area2 > 0;

    const result = [];
    for (let i = 0; i < n; i++) {
      const pPrev = polygon[(i + n - 1) % n];
      const pCurr = polygon[i];
      const pNext = polygon[(i + 1) % n];

      const insetPrev = edgeInsets[(i + n - 1) % n];
      const insetCurr = edgeInsets[i];

      // Edge directions
      let e1x = pCurr.x - pPrev.x, e1y = pCurr.y - pPrev.y;
      let e2x = pNext.x - pCurr.x, e2y = pNext.y - pCurr.y;
      const e1len = Math.hypot(e1x, e1y) || 1e-6;
      const e2len = Math.hypot(e2x, e2y) || 1e-6;
      e1x /= e1len; e1y /= e1len; e2x /= e2len; e2y /= e2len;

      // Inward normals depend on orientation
      const n1x = ccw ? -e1y : e1y;
      const n1y = ccw ?  e1x : -e1x;
      const n2x = ccw ? -e2y : e2y;
      const n2y = ccw ?  e2x : -e2x;

      // Offset lines parallel to edges
      const q1x = pCurr.x + n1x * insetPrev;
      const q1y = pCurr.y + n1y * insetPrev;
      const q2x = pCurr.x + n2x * insetCurr;
      const q2y = pCurr.y + n2y * insetCurr;

      // Intersect (q1 + t1*e1) with (q2 + t2*e2)
      const det = e1x * (-e2y) - e1y * (-e2x); // e1 x (-e2)
      if (Math.abs(det) < 1e-6) {
        // Parallel; advance slightly along bisector as fallback
        const bx = (n1x + n2x) * 0.5, by = (n1y + n2y) * 0.5;
        result.push(new Point(pCurr.x + bx * Math.max(insetPrev, insetCurr), pCurr.y + by * Math.max(insetPrev, insetCurr)));
        continue;
      }
      // Solve q1 + t1*e1 = q2 + t2*e2  =>  t1 = ((q2-q1) x (-e2)) / (e1 x (-e2))
      const dx = q2x - q1x, dy = q2y - q1y;
      const num = dx * (-e2y) - dy * (-e2x);
      const t1 = num / det;
      const ix = q1x + e1x * t1;
      const iy = q1y + e1y * t1;
      result.push(new Point(ix, iy));
    }
    return result;
  }

  // Clip polygon to another polygon (keep INSIDE of clip), Sutherland–Hodgman
  clipInside(polygon, clipPoly) {
    if (!polygon || polygon.length < 3) return polygon;
    if (!clipPoly || clipPoly.length < 3) return polygon;

    const isLeft = (a, b, p) => (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x);
    const intersect = (a, b, c, d) => {
      const r = { x: b.x - a.x, y: b.y - a.y };
      const s = { x: d.x - c.x, y: d.y - c.y };
      const denom = r.x * s.y - r.y * s.x;
      if (Math.abs(denom) < 1e-8) return b; // parallel fallback
      const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
      return new Point(a.x + t * r.x, a.y + t * r.y);
    };

    let output = polygon.slice();
    for (let i = 0; i < clipPoly.length; i++) {
      const A = clipPoly[i];
      const B = clipPoly[(i + 1) % clipPoly.length];
      const input = output;
      output = [];
      if (input.length === 0) break;
      for (let j = 0; j < input.length; j++) {
        const P = input[j];
        const Q = input[(j + 1) % input.length];
        const Pside = isLeft(A, B, P);
        const Qside = isLeft(A, B, Q);
        const Pin = Pside >= 0;
        const Qin = Qside >= 0;
        if (Pin && Qin) {
          output.push(Q);
        } else if (Pin && !Qin) {
          output.push(intersect(P, Q, A, B));
        } else if (!Pin && Qin) {
          output.push(intersect(P, Q, A, B));
          output.push(Q);
        }
      }
    }
    return output.length >= 3 ? output : polygon;
  }

  // Clip polygon to the OUTSIDE of clipPoly (subtract clipPoly)
  clipOutside(polygon, clipPoly) {
    return this.subtractPolygon(polygon, clipPoly);
  }
  
  /**
   * Create a regular polygon (circle approximation)
   */
  createRegularPolygon(sides, radius, center) {
    const polygon = [];
    for (let i = 0; i < sides; i++) {
      const angle = (i / sides) * Math.PI * 2;
      polygon.push(new Point(
        center.x + Math.cos(angle) * radius,
        center.y + Math.sin(angle) * radius
      ));
    }
    return polygon;
  }
  
  /**
   * Subtract one polygon from another (simple vertex filtering for circles)
   * Implements Sutherland–Hodgman style clipping that keeps the area OUTSIDE
   * the convex 'circle' polygon (which is a regular n-gon approximation).
   */
  subtractPolygon(polygon, circle) {
    if (!polygon || polygon.length < 3) return polygon;
    if (!circle || circle.length < 3) return polygon;

    // Determine orientation of the circle polygon (assumed CCW)
    let area2 = 0;
    for (let i = 0; i < circle.length; i++) {
      const a = circle[i];
      const b = circle[(i + 1) % circle.length];
      area2 += a.x * b.y - b.x * a.y;
    }
    const ccw = area2 > 0;

    const isLeft = (a, b, p) => (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x);
    const intersect = (a, b, c, d) => {
      // line ab with cd
      const r = { x: b.x - a.x, y: b.y - a.y };
      const s = { x: d.x - c.x, y: d.y - c.y };
      const denom = r.x * s.y - r.y * s.x;
      if (Math.abs(denom) < 1e-8) return b; // parallel fallback
      const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
      return new Point(a.x + t * r.x, a.y + t * r.y);
    };

    let output = polygon.slice();
    // For outside-clip we keep points that are NOT inside each edge half-plane
    for (let i = 0; i < circle.length; i++) {
      const A = circle[i];
      const B = circle[(i + 1) % circle.length];
      const input = output;
      output = [];
      if (input.length === 0) break;
      for (let j = 0; j < input.length; j++) {
        const P = input[j];
        const Q = input[(j + 1) % input.length];
        const Pside = isLeft(A, B, P);
        const Qside = isLeft(A, B, Q);
        // For CCW clip polygon, inside is left (>=0). We want OUTSIDE.
        const Pin = ccw ? Pside <= 0 : Pside >= 0;
        const Qin = ccw ? Qside <= 0 : Qside >= 0;
        if (Pin && Qin) {
          // both outside -> keep Q only
          output.push(Q);
        } else if (Pin && !Qin) {
          // leaving outside -> add intersection
          output.push(intersect(P, Q, A, B));
        } else if (!Pin && Qin) {
          // entering outside -> add intersection+Q
          output.push(intersect(P, Q, A, B));
          output.push(Q);
        } else {
          // both inside (of clip polygon) -> keep nothing
        }
      }
    }
    return output.length >= 3 ? output : polygon;
  }

  buildGeometry() {
    const availableShape = this.getAvailable();
    
    if (!availableShape || availableShape.length < 3) {
      console.warn('Ward.buildGeometry: Invalid availableShape, using original patch shape');
      this.geometry = [];
      return;
    }
    
    // Store the inset shape for rendering ward backgrounds
    this.availableShape = availableShape;
    
    // Check lots mode early
    // Check lots mode early - handle string values and mix mode
    let lots;
    if (StateManager.lotsMode === 'mix') {
      lots = Random.chance(0.5); // 50% chance for lots vs normal in mix mode
    } else if (StateManager.lotsMode === 'lots' || StateManager.lotsMode === true) {
      lots = true;
    } else {
      lots = false;
    }
    // If this patch borders roads, create a thin ring of buildings hugging the road first
    // SKIP in lots mode to avoid double-stacking buildings at perimeters
    // SKIP inside the city (withinCity=true) to avoid houses along roads in normal mode
    let roadBuildings = [];
    if (!lots && !this.patch.withinCity && this.patch.face && this.patch.face.edge) {
      const loop = this.patch.face.loop();
      const streetWidth = (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0;
      const buildingDepth = 6.0; // average building depth toward interior
      for (let i = 0; i < loop.length; i++) {
        const e = loop[i].e; if (e.data !== EdgeType.ROAD) continue;
        const a = loop[i].v, b = loop[(i+1)%loop.length].v;
        const dx = b.x - a.x, dy = b.y - a.y; const len = Math.hypot(dx,dy)||1e-6; const nx = -dy/len, ny = dx/len;
        const gap = (StateManager.buildingGap !== undefined) ? StateManager.buildingGap : 1.8;
        const inset = streetWidth/2 + gap; // start line just inside the street
        const stripOut = inset + 0.5; // outer edge of strip (near street)
        const stripIn = inset + buildingDepth; // inner edge toward interior
        const p1 = new Point(a.x + nx*stripOut, a.y + ny*stripOut);
        const p2 = new Point(b.x + nx*stripOut, b.y + ny*stripOut);
        const p3 = new Point(b.x + nx*stripIn, b.y + ny*stripIn);
        const p4 = new Point(a.x + nx*stripIn, a.y + ny*stripIn);
        // Chop the strip into row buildings along the edge
        const target = 5.5; // target facade width
        const count = Math.max(1, Math.floor(len/target));
        for (let k=0;k<count;k++){
          const t0=k/count, t1=(k+1)/count;
          const s1 = new Point(p1.x + (p2.x-p1.x)*t0, p1.y + (p2.y-p1.y)*t0);
          const s2 = new Point(p1.x + (p2.x-p1.x)*t1, p1.y + (p2.y-p1.y)*t1);
          const s3 = new Point(p4.x + (p3.x-p4.x)*t1, p4.y + (p3.y-p4.y)*t1);
          const s4 = new Point(p4.x + (p3.x-p4.x)*t0, p4.y + (p3.y-p4.y)*t0);
          roadBuildings.push([s1,s2,s3,s4]);
        }
      }
    }
    
    // Filter out roadBuildings that intersect water bodies - don't generate slivers
    if (roadBuildings.length > 0 && Array.isArray(this.model.waterBodies) && this.model.waterBodies.length > 0) {
      roadBuildings = roadBuildings.filter(building => {
        // Check if building centre is in water
        if (!building || building.length < 3) return false;
        const center = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
        center.x /= building.length;
        center.y /= building.length;
        
        // Point-in-polygon test against each water body
        for (const water of this.model.waterBodies) {
          if (!water || water.length < 3) continue;
          let inside = false;
          for (let i = 0, j = water.length - 1; i < water.length; j = i++) {
            const xi = water[i].x, yi = water[i].y;
            const xj = water[j].x, yj = water[j].y;
            const intersect = ((yi > center.y) !== (yj > center.y)) && 
                            (center.x < (xj - xi) * (center.y - yi) / (yj - yi) + xi);
            if (intersect) inside = !inside;
          }
          if (inside) return false; // Building centre is in water - reject it
        }
        return true; // Building doesn't intersect water
      });
    }


    // Lots mode uses MUCH smaller minimum size for tight tessellation
    // Normal mode uses larger buildings with more organic shapes
    const minSq = lots ? 8 : 25;
    const gridChaos = this.model.gridChaos !== undefined ? this.model.gridChaos : 0.4;
    const sizeChaos = this.model.sizeChaos !== undefined ? this.model.sizeChaos : 0.6;
    
    // Random chance to create an open piazza instead of buildings
    if (Random.chance(StateManager.plazaChance)) {
      // Create piazza with buildings around perimeter and empty centre
      this.geometry = this.createPiazza(availableShape);
    } else {
      // Normal ward with buildings
      const innerBuildings = this.createAlleys(availableShape, minSq, gridChaos, sizeChaos, true);
      this.geometry = roadBuildings.length ? roadBuildings.concat(innerBuildings) : innerBuildings;
    }
    
    // Filter buildings: check each vertex, push wet ones out of water AWAY from water centre
    if (this.geometry && this.geometry.length > 0 && Array.isArray(this.model.waterBodies) && this.model.waterBodies.length > 0) {
      const pointInPoly = (pt, poly) => {
        let inside = false;
        for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
          const xi = poly[i].x, yi = poly[i].y;
          const xj = poly[j].x, yj = poly[j].y;
          const intersect = ((yi > pt.y) !== (yj > pt.y)) && 
                          (pt.x < (xj - xi) * (pt.y - yi) / (yj - yi) + xi);
          if (intersect) inside = !inside;
        }
        return inside;
      };
      
      if (!this.model.waterfrontBuildings) this.model.waterfrontBuildings = [];

      // Cache water polygon metadata for faster queries
      if (!this.model._waterCache || this.model._waterCache.length !== this.model.waterBodies.length) {
        this.model._waterCache = this.model.waterBodies
          .filter(w => w && w.length >= 3)
          .map(poly => {
            // AABB
            let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
            for (const p of poly) { if (p.x < minX) minX = p.x; if (p.y < minY) minY = p.y; if (p.x > maxX) maxX = p.x; if (p.y > maxY) maxY = p.y; }
            // Precompute edges and PIP helpers
            const edges = [];
            for (let i = 0; i < poly.length; i++) {
              const a = poly[i];
              const b = poly[(i + 1) % poly.length];
              const dx = b.x - a.x, dy = b.y - a.y;
              const len2 = dx*dx + dy*dy;
              const slopeInv = Math.abs(b.y - a.y) > 1e-12 ? (b.x - a.x) / (b.y - a.y) : 0;
              edges.push({ ax: a.x, ay: a.y, bx: b.x, by: b.y, dx, dy, len2, slopeInv });
            }
            return { poly, minX, minY, maxX, maxY, edges };
          });
      }

      const aabbOverlap = (a, b) => !(a.maxX < b.minX || a.minX > b.maxX || a.maxY < b.minY || a.minY > b.maxY);
      const pipFast = (pt, meta) => {
        if (pt.x < meta.minX || pt.x > meta.maxX || pt.y < meta.minY || pt.y > meta.maxY) return false;
        let inside = false;
        const y = pt.y;
        for (const e of meta.edges) {
          const yi = e.ay, yj = e.by;
          // ((yi > y) !== (yj > y))
          const aboveDiff = ((yi > y) !== (yj > y));
          if (aboveDiff) {
            const xInt = e.ax + e.slopeInv * (y - yi);
            if (pt.x < xInt) inside = !inside;
          }
        }
        return inside;
      };
      const nearestProjectionMeta = (p, meta) => {
        let minD = Infinity, projPt = p, eDX = 1, eDY = 0;
        for (const e of meta.edges) {
          if (e.len2 < 1e-12) continue;
          let t = ((p.x - e.ax) * e.dx + (p.y - e.ay) * e.dy) / e.len2;
          t = Math.max(0, Math.min(1, t));
          const px = e.ax + t * e.dx;
          const py = e.ay + t * e.dy;
          const d = Math.hypot(p.x - px, p.y - py);
          if (d < minD) { minD = d; projPt = new Point(px, py); eDX = e.dx; eDY = e.dy; }
        }
        return { projPt, eDX, eDY, minD };
      };

      const newGeometry = [];
      for (const building of this.geometry) {
        if (!building || building.length < 3) continue;

        // Building AABB
        let bminX = Infinity, bminY = Infinity, bmaxX = -Infinity, bmaxY = -Infinity;
        for (const p of building) { if (p.x < bminX) bminX = p.x; if (p.y < bminY) bminY = p.y; if (p.x > bmaxX) bmaxX = p.x; if (p.y > bmaxY) bmaxY = p.y; }
        const bAABB = { minX: bminX, minY: bminY, maxX: bmaxX, maxY: bmaxY };

        // Collect candidate waters by AABB overlap (with small margin)
        const margin = 1.0;
        const expanded = { minX: bminX - margin, minY: bminY - margin, maxX: bmaxX + margin, maxY: bmaxY + margin };
        const candidates = [];
        for (const meta of this.model._waterCache) {
          if (aabbOverlap(expanded, meta)) candidates.push(meta);
        }

        if (candidates.length === 0) {
          newGeometry.push(building); // nowhere near water
          continue;
        }

        // Pick the water meta with the most vertices inside (best overlap)
        const totalVerts = building.length;
        let bestMeta = null; let bestInside = 0;
        for (const meta of candidates) {
          let insideC = 0;
          // Early skip if AABB fully outside
          for (const v of building) { if (pipFast(v, meta)) insideC++; }
          if (insideC > bestInside) { bestInside = insideC; bestMeta = meta; }
          if (insideC >= totalVerts) break; // fully inside, can't get better
        }

        if (!bestMeta || bestInside === 0) {
          newGeometry.push(building); // no overlap after all
          continue;
        }

        // Elide if all or all-but-one vertices are inside this water
        if (bestInside >= totalVerts - 1) {
          continue;
        }

        // Translate whole building using displacements of wet vertices to nearest boundary
        let sumDx = 0, sumDy = 0, wetCount = 0;
        let nearestOnBoundary = null; let nearestEdge = { dx: 1, dy: 0 }; let nearestDist = Infinity;
        for (const v of building) {
          if (!pipFast(v, bestMeta)) continue;
          const { projPt, eDX, eDY, minD } = nearestProjectionMeta(v, bestMeta);
          sumDx += projPt.x - v.x; sumDy += projPt.y - v.y; wetCount++;
          if (minD < nearestDist) { nearestDist = minD; nearestOnBoundary = projPt; nearestEdge = { dx: eDX, dy: eDY }; }
        }

        // If centroid is in water but no vertex was (thin case)
        if (wetCount === 0) {
          const center = building.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
          center.x /= totalVerts; center.y /= totalVerts;
          if (center.x >= bestMeta.minX && center.x <= bestMeta.maxX && center.y >= bestMeta.minY && center.y <= bestMeta.maxY && pipFast(center, bestMeta)) {
            const { projPt, eDX, eDY } = nearestProjectionMeta(center, bestMeta);
            sumDx += projPt.x - center.x; sumDy += projPt.y - center.y; wetCount = 1;
            nearestOnBoundary = projPt; nearestEdge = { dx: eDX, dy: eDY };
          }
        }

        let tx = 0, ty = 0; if (wetCount > 0) { tx = sumDx / wetCount; ty = sumDy / wetCount; }
        const elen = Math.hypot(nearestEdge.dx, nearestEdge.dy) || 1;
        let nx = -nearestEdge.dy / elen; let ny = nearestEdge.dx / elen; const eps = 0.8;
        const pTest = new Point(nearestOnBoundary.x + nx * eps, nearestOnBoundary.y + ny * eps);
        if (pipFast(pTest, bestMeta)) { nx = -nx; ny = -ny; }

        const adjustedBuilding = building.map(p => new Point(p.x + tx + nx * eps, p.y + ty + ny * eps));
        newGeometry.push(adjustedBuilding);

        // Waterfront feature
        if (nearestOnBoundary) {
          const edgeLen = Math.hypot(nearestEdge.dx, nearestEdge.dy);
          if (edgeLen > 0.5) {
            const ux = nearestEdge.dx / edgeLen, uy = nearestEdge.dy / edgeLen;
            const wx = -nx, wy = -ny; const mid = nearestOnBoundary;
            const featureType = Random.int(0, 2);
            if (!this.model.waterfrontBuildings) this.model.waterfrontBuildings = [];
            if (featureType === 0) {
              const w = 2.0, d = 2.4;
              const a = new Point(mid.x - ux*w*0.5, mid.y - uy*w*0.5);
              const b = new Point(mid.x + ux*w*0.5, mid.y + uy*w*0.5);
              const c = new Point(b.x + wx*d, b.y + wy*d);
              const dpt = new Point(a.x + wx*d, a.y + wy*d);
              this.model.waterfrontBuildings.push({feature:'dock', geometry:[a,b,c,dpt]});
            } else if (featureType === 1) {
              const post = new Point(mid.x + wx*1.4, mid.y + wy*1.4);
              this.model.waterfrontBuildings.push({feature:'post', geometry:post});
            } else {
              const boatCenter = new Point(mid.x + wx*2.0, mid.y + wy*2.0);
              const boat = [
                new Point(boatCenter.x - ux*1.2,  boatCenter.y - uy*1.2),
                new Point(boatCenter.x + ux*1.2,  boatCenter.y + uy*1.2),
                new Point(boatCenter.x + ux*0.8 + wx*0.6, boatCenter.y + uy*0.8 + wy*0.6),
                new Point(boatCenter.x - ux*0.8 + wx*0.6, boatCenter.y - uy*0.8 + wy*0.6)
              ];
              this.model.waterfrontBuildings.push({feature:'boat', geometry:boat});
            }
          }
        }
      }
      this.geometry = newGeometry;
    }
  }

  createPiazza(polygon) {
    // Create ring of buildings around the perimeter with open centre
    const buildings = [];
    const minSq = 20;
    const gridChaos = this.model.gridChaos || 0.2;
    const sizeChaos = this.model.sizeChaos || 0.3;
    
    // Calculate centre
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

  createAlleys(polygon, minSq, gridChaos, sizeChaos, split, depth = 0) {
    const maxDepth = StateManager.lotsMode ? 12 : 10;
    const area0 = this.polygonArea(polygon);
    if (!polygon || polygon.length < 3 || area0 <= 0.001 || depth >= maxDepth) {
      return area0 > 0 ? [polygon] : [];
    }
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
    // If cut failed (returned one half equal to original), avoid infinite recursion
    if (!halves || halves.length < 2) {
      // If we cannot split, either accept as building or stop
      if (area0 < minSq) return [polygon];
      // As a fallback, shrink slightly and accept
      const center = polygon.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
      center.x/=polygon.length; center.y/=polygon.length;
      const shrunk = polygon.map(p=>new Point(center.x+(p.x-center.x)*0.98, center.y+(p.y-center.y)*0.98));
      return [shrunk];
    }
    
    const buildings = [];
    for (const half of halves) {
      const area = this.polygonArea(half);
      const sizeVariation = Math.pow(2, 4 * sizeChaos * (Random.float() - 0.5));
      if (area < minSq * sizeVariation) {
        // Small enough - make it a building (skip some for empty lots)
        const skipChance = StateManager.lotsMode ? 0.0 : 0.04;
        if (Random.float() > skipChance) {
          // Inset the building from its lot boundary to prevent overlaps
          const inset = StateManager.lotsMode ? 0.8 : 0.3; // More inset in lots mode
          const center = half.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
          center.x /= half.length;
          center.y /= half.length;
          const insetBuilding = half.map(p => new Point(
            center.x + (p.x - center.x) * (1 - inset / 10),
            center.y + (p.y - center.y) * (1 - inset / 10)
          ));
          buildings.push(insetBuilding);
        }
      } else {
        // Keep subdividing
        const shouldSplit = StateManager.lotsMode ? (area > minSq * 1.25) : (area > minSq / (Random.float() * Random.float()));
        if (shouldSplit) {
          buildings.push(...this.createAlleys(half, minSq, gridChaos, sizeChaos, shouldSplit, depth + 1));
        } else {
          // Final building - apply inset
          const inset = StateManager.lotsMode ? 0.8 : 0.3;
          const center = half.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
          center.x /= half.length;
          center.y /= half.length;
          const insetBuilding = half.map(p => new Point(
            center.x + (p.x - center.x) * (1 - inset / 10),
            center.y + (p.y - center.y) * (1 - inset / 10)
          ));
          buildings.push(insetBuilding);
        }
      }
    }
    
    return buildings;
  }

  cutPolygon(poly, p1, p2, gap = 0) {

    const x1 = p1.x, y1 = p1.y;
    const dx1 = p2.x - x1, dy1 = p2.y - y1;
    
    const len = poly.length;
    let edge1 = 0, ratio1 = 0.0;
    let edge2 = 0, ratio2 = 0.0;
    let count = 0;
    
    // Find intersections with polygon edges
    for (let i = 0; i < len; i++) {
      const v0 = poly[i];
      const v1 = poly[(i + 1) % len];
      
      const x2 = v0.x, y2 = v0.y;
      const dx2 = v1.x - x2, dy2 = v1.y - y2;
      
      const denom = dx1 * dy2 - dy1 * dx2;
      if (Math.abs(denom) > 0.001) {
        const t = ((x2 - x1) * dy2 - (y2 - y1) * dx2) / denom;
        const u = ((x2 - x1) * dy1 - (y2 - y1) * dx1) / denom;
        
        if (u >= 0 && u <= 1) {
          if (count === 0) { edge1 = i; ratio1 = t; }
          else if (count === 1) { edge2 = i; ratio2 = t; }
          count++;
        }
      }
    }
    
    if (count !== 2) return [poly];
    
    // Calculate intersection points
    const point1 = new Point(
      p1.x + (p2.x - p1.x) * ratio1,
      p1.y + (p2.y - p1.y) * ratio1
    );
    const point2 = new Point(
      p1.x + (p2.x - p1.x) * ratio2,
      p1.y + (p2.y - p1.y) * ratio2
    );
    
    // Build half1: vertices from edge1+1 to edge2, with intersection points
    const half1 = [];
    half1.push(point1);
    for (let i = edge1 + 1; i <= edge2; i++) {
      half1.push(poly[i]);
    }
    half1.push(point2);
    
    // Build half2: vertices from edge2+1 to end, then 0 to edge1, with intersection points
    const half2 = [];
    half2.push(point2);
    for (let i = edge2 + 1; i < len; i++) {
      half2.push(poly[i]);
    }
    for (let i = 0; i <= edge1; i++) {
      half2.push(poly[i]);
    }
    half2.push(point1);
    
    // Apply gap using peel if needed
    if (gap > 0) {
      return [
        this.peelPolygon(half1, point2, gap / 2),
        this.peelPolygon(half2, point1, gap / 2)
      ].filter(h => h && h.length >= 3 && Math.abs(this.polygonArea(h)) > 0.01);
    }
    
    return [half1, half2].filter(h => h.length >= 3 && Math.abs(this.polygonArea(h)) > 0.01);
  }
  
  peelPolygon(poly, v1, d) {

    const i1 = poly.findIndex(p => Math.abs(p.x - v1.x) < 0.001 && Math.abs(p.y - v1.y) < 0.001);
    if (i1 === -1) return poly;
    
    const i2 = i1 === poly.length - 1 ? 0 : i1 + 1;
    const v2 = poly[i2];
    
    // Vector along edge
    const vx = v2.x - v1.x;
    const vy = v2.y - v1.y;
    
    // Perpendicular (rotate 90deg counterclockwise: (x,y) -> (-y,x))
    const len = Math.sqrt(vx * vx + vy * vy);
    if (len < 0.001) return poly;
    const nx = -vy / len * d;
    const ny = vx / len * d;
    
    // Cut line parallel to edge, offset by perpendicular
    const cutP1 = new Point(v1.x + nx, v1.y + ny);
    const cutP2 = new Point(v2.x + nx, v2.y + ny);
    
    // Use basic cut with NO gap (0) and return first half
    const halves = this.cutPolygonNoGap(poly, cutP1, cutP2);
    return halves[0];
  }
  
  cutPolygonNoGap(poly, p1, p2) {
    // Version of cut without gap for use in peel
    const x1 = p1.x, y1 = p1.y;
    const dx1 = p2.x - x1, dy1 = p2.y - y1;
    
    const len = poly.length;
    let edge1 = 0, ratio1 = 0.0;
    let edge2 = 0, ratio2 = 0.0;
    let count = 0;
    
    for (let i = 0; i < len; i++) {
      const v0 = poly[i];
      const v1 = poly[(i + 1) % len];
      
      const x2 = v0.x, y2 = v0.y;
      const dx2 = v1.x - x2, dy2 = v1.y - y2;
      
      const denom = dx1 * dy2 - dy1 * dx2;
      if (Math.abs(denom) > 0.001) {
        const t = ((x2 - x1) * dy2 - (y2 - y1) * dx2) / denom;
        const u = ((x2 - x1) * dy1 - (y2 - y1) * dx1) / denom;
        
        if (u >= 0 && u <= 1) {
          if (count === 0) { edge1 = i; ratio1 = t; }
          else if (count === 1) { edge2 = i; ratio2 = t; }
          count++;
        }
      }
    }
    
    if (count !== 2) return [poly];
    
    const point1 = new Point(p1.x + (p2.x - p1.x) * ratio1, p1.y + (p2.y - p1.y) * ratio1);
    const point2 = new Point(p1.x + (p2.x - p1.x) * ratio2, p1.y + (p2.y - p1.y) * ratio2);
    
    const half1 = [point1];
    for (let i = edge1 + 1; i <= edge2; i++) half1.push(poly[i]);
    half1.push(point2);
    
    const half2 = [point2];
    for (let i = edge2 + 1; i < len; i++) half2.push(poly[i]);
    for (let i = 0; i <= edge1; i++) half2.push(poly[i]);
    half2.push(point1);
    
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
      'craftsmen': 'Craftsmen',
      'merchant': 'Merchant',
      'slum': 'Slums',
      'patriciate': 'Patriciate',
      'administration': 'Administration',
      'military': 'Military',
      'park': 'Park'
    };
    return labels[this.wardType] || '';
  }
  
  shrinkPolygon(poly, amount) {
    // Inset polygon - calls overridable implementation
    if (!poly || poly.length < 3 || amount <= 0) return poly;
    return this.shrinkPolygonImpl(poly, amount);
  }
  
  shrinkPolygonImpl(poly, amount) {
    // Default: distance-based shrinking (inset by fixed amount)
    const center = poly.reduce((acc, p) => ({ x: acc.x + p.x, y: acc.y + p.y }), { x: 0, y: 0 });
    center.x /= poly.length;
    center.y /= poly.length;
    
    const shrunk = [];
    for (let i = 0; i < poly.length; i++) {
      const p = poly[i];
      const dx = p.x - center.x;
      const dy = p.y - center.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      
      if (dist > amount) {
        const factor = (dist - amount) / dist;
        shrunk.push(new Point(
          center.x + dx * factor,
          center.y + dy * factor
        ));
      } else {
        shrunk.push(new Point(center.x, center.y));
      }
    }
    
    return shrunk.length >= 3 ? shrunk : poly;
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
    
    // Add corner towers - size scales with wallThickness
    const wallThickness = (StateManager.wallThickness !== undefined) ? StateManager.wallThickness : 5;
    const towerSize = wallThickness * 0.6;
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
    
    // Find gate position (towards centre of city)
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
    
    this.geometry = buildings;
    this.towers = towers;

    // Ensure castles respect water like other wards: clip walls, adjust/elide towers and keep buildings
    if (Array.isArray(this.model.waterBodies) && this.model.waterBodies.length > 0) {
      // Reuse or build water cache
      if (!this.model._waterCache || this.model._waterCache.length !== this.model.waterBodies.length) {
        this.model._waterCache = this.model.waterBodies
          .filter(w => w && w.length >= 3)
          .map(poly => {
            let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
            for (const p of poly) { if (p.x < minX) minX = p.x; if (p.y < minY) minY = p.y; if (p.x > maxX) maxX = p.x; if (p.y > maxY) maxY = p.y; }
            const edges = [];
            for (let i = 0; i < poly.length; i++) {
              const a = poly[i];
              const b = poly[(i + 1) % poly.length];
              const dx = b.x - a.x, dy = b.y - a.y;
              const len2 = dx*dx + dy*dy;
              const slopeInv = Math.abs(b.y - a.y) > 1e-12 ? (b.x - a.x) / (b.y - a.y) : 0;
              edges.push({ ax: a.x, ay: a.y, bx: b.x, by: b.y, dx, dy, len2, slopeInv });
            }
            return { poly, minX, minY, maxX, maxY, edges };
          });
      }

      const aabbOverlap = (a, b) => !(a.maxX < b.minX || a.minX > b.maxX || a.maxY < b.minY || a.minY > b.maxY);
      const pipFast = (pt, meta) => {
        if (pt.x < meta.minX || pt.x > meta.maxX || pt.y < meta.minY || pt.y > meta.maxY) return false;
        let inside = false; const y = pt.y;
        for (const e of meta.edges) {
          const yi = e.ay, yj = e.by; if (((yi > y) !== (yj > y))) {
            const xInt = e.ax + e.slopeInv * (y - yi); if (pt.x < xInt) inside = !inside;
          }
        }
        return inside;
      };
      const nearestProjectionMeta = (p, meta) => {
        let minD = Infinity, projPt = p, eDX = 1, eDY = 0;
        for (const e of meta.edges) {
          if (e.len2 < 1e-12) continue;
          let t = ((p.x - e.ax) * e.dx + (p.y - e.ay) * e.dy) / e.len2;
          t = Math.max(0, Math.min(1, t));
          const px = e.ax + t * e.dx; const py = e.ay + t * e.dy;
          const d = Math.hypot(p.x - px, p.y - py);
          if (d < minD) { minD = d; projPt = new Point(px, py); eDX = e.dx; eDY = e.dy; }
        }
        return { projPt, eDX, eDY, minD };
      };

      // 1) Clip citadel wall against water so it never renders over water
      if (this.citadelWall && this.citadelWall.length >= 3) {
        let wall = this.citadelWall;
        for (const meta of this.model._waterCache) {
          const before = wall; // keep ref
          const clipped = this.clipOutside(wall, meta.poly);
          if (clipped && clipped.length >= 3) wall = clipped;
        }
        this.citadelWall = wall;
      }

      // Helper to adjust a list of polygons like buildings (no waterfront features for castle)
      const adjustPolys = (polys) => {
        const out = [];
        for (const poly of polys) {
          if (!poly || poly.length < 3) continue;
          // AABB
          let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
          for (const p of poly) { if (p.x < minX) minX = p.x; if (p.y < minY) minY = p.y; if (p.x > maxX) maxX = p.x; if (p.y > maxY) maxY = p.y; }
          const margin = 1.0; const expanded = { minX: minX - margin, minY: minY - margin, maxX: maxX + margin, maxY: maxY + margin };
          const candidates = [];
          for (const meta of this.model._waterCache) { if (aabbOverlap(expanded, meta)) candidates.push(meta); }
          if (candidates.length === 0) { out.push(poly); continue; }

          const totalVerts = poly.length; let bestMeta = null; let bestInside = 0;
          for (const meta of candidates) {
            let insideC = 0; for (const v of poly) { if (pipFast(v, meta)) insideC++; }
            if (insideC > bestInside) { bestInside = insideC; bestMeta = meta; }
            if (insideC >= totalVerts) break;
          }
          if (!bestMeta || bestInside === 0) { out.push(poly); continue; }
          if (bestInside >= totalVerts - 1) { continue; } // elide mostly submerged

          let sumDx = 0, sumDy = 0, wetCount = 0; let nearestOnBoundary = null; let nearestEdge = { dx: 1, dy: 0 }; let nearestDist = Infinity;
          for (const v of poly) {
            if (!pipFast(v, bestMeta)) continue;
            const { projPt, eDX, eDY, minD } = nearestProjectionMeta(v, bestMeta);
            sumDx += projPt.x - v.x; sumDy += projPt.y - v.y; wetCount++;
            if (minD < nearestDist) { nearestDist = minD; nearestOnBoundary = projPt; nearestEdge = { dx: eDX, dy: eDY }; }
          }
          if (wetCount === 0) { out.push(poly); continue; }
          const elen = Math.hypot(nearestEdge.dx, nearestEdge.dy) || 1; let nx = -nearestEdge.dy / elen; let ny = nearestEdge.dx / elen; const eps = 0.8;
          const tx = sumDx / wetCount, ty = sumDy / wetCount;
          const pTest = new Point(nearestOnBoundary.x + nx * eps, nearestOnBoundary.y + ny * eps);
          if (pipFast(pTest, bestMeta)) { nx = -nx; ny = -ny; }
          const moved = poly.map(p => new Point(p.x + tx + nx * eps, p.y + ty + ny * eps));
          out.push(moved);

          // Add waterfront feature for castle elements as well (dock/post/boat)
          if (nearestOnBoundary) {
            if (!this.model.waterfrontBuildings) this.model.waterfrontBuildings = [];
            const edgeLen = Math.hypot(nearestEdge.dx, nearestEdge.dy);
            if (edgeLen > 0.5) {
              const ux = nearestEdge.dx / edgeLen, uy = nearestEdge.dy / edgeLen;
              // normal points into water if we flip from land normal
              const wx = -nx, wy = -ny;
              const mid = nearestOnBoundary;
              const featureType = Random.int(0, 2);
              if (featureType === 0) {
                const w = 2.0, d = 2.4;
                const a = new Point(mid.x - ux*w*0.5, mid.y - uy*w*0.5);
                const b = new Point(mid.x + ux*w*0.5, mid.y + uy*w*0.5);
                const c = new Point(b.x + wx*d, b.y + wy*d);
                const dpt = new Point(a.x + wx*d, a.y + wy*d);
                this.model.waterfrontBuildings.push({feature:'dock', geometry:[a,b,c,dpt]});
              } else if (featureType === 1) {
                const post = new Point(mid.x + wx*1.4, mid.y + wy*1.4);
                this.model.waterfrontBuildings.push({feature:'post', geometry:post});
              } else {
                const boatCenter = new Point(mid.x + wx*2.0, mid.y + wy*2.0);
                const boat = [
                  new Point(boatCenter.x - ux*1.2,  boatCenter.y - uy*1.2),
                  new Point(boatCenter.x + ux*1.2,  boatCenter.y + uy*1.2),
                  new Point(boatCenter.x + ux*0.8 + wx*0.6, boatCenter.y + uy*0.8 + wy*0.6),
                  new Point(boatCenter.x - ux*0.8 + wx*0.6, boatCenter.y - uy*0.8 + wy*0.6)
                ];
                this.model.waterfrontBuildings.push({feature:'boat', geometry:boat});
              }
            }
          }
        }
        return out;
      };

      // 2) Adjust castle buildings and towers
      this.geometry = adjustPolys(this.geometry);
      this.towers = adjustPolys(this.towers);
    }
  }

  shrinkPolygonImpl(poly, amount) {
    // Castle: percentage-based shrinking
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

  shrinkPolygonImpl(poly, amount) {
    // Cathedral: percentage-based shrinking
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
    // Lazy tree generation using Poisson-disk sampling
    if (this.trees !== null) return this.trees;
    this.trees = [];
    const poly = (this.availableShape && this.availableShape.length>=3) ? this.availableShape : this.shape;
    if (!poly || poly.length < 3) return this.trees;
    const baseSpacing = 2.6; // slightly tighter than global
    const densityFn = (p)=>{
      // Parks: modulate lightly with noise for clumps
      const n = (PerlinNoise.noise(p.x * 0.08, p.y * 0.08) + 1) * 0.5; // 0..1
      return baseSpacing * (0.8 + 0.6 * n);
    };
    const points = CityRenderer.poissonSample(poly, densityFn, 25);
    for (const point of points) {
      this.trees.push({ pos: point, crown: this.getTreeCrown() });
    }
    return this.trees;
  }
  
  fillAreaWithPattern(polygon) {
    // Simplified Poisson disk sampling for polygon
    //
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
    // Generate a random tree crown polygon
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
    // Slums have organic clusters of buildings along alleyway curves
    
    // Get ALL exterior alley paths - don't filter by distance
    const relevantAlleys = [];
    
    if (this.model.exteriorRoads) {
      for (const road of this.model.exteriorRoads) {
        if (road.isAlley) {
          relevantAlleys.push(road);
        }
      }
    }
    
    // Create organic clusters along alleys using box packing
    this.geometry = this.createOrganicClustersAlongAlleys(this.shape, relevantAlleys);
  }
  
  createOrganicClustersAlongAlleys(wardShape, alleys) {
    if (!alleys || alleys.length === 0) {
      // No alleys - sparse scattered buildings
      const shrunkBlock = this.shrinkPolygon(wardShape, 2);
      const buildings = this.createAlleys(shrunkBlock, 12, 0.15, 0.25, Random.chance(0.2));
      // Keep only 30% for sparse straggling effect
      return buildings.filter(() => Random.float() < 0.3);
    }
    
    const buildings = [];
    const alleyWidth = this.model.alleyWidth || 1.8;
    
    // Find streets (non-alley roads)
    const streets = (this.model.exteriorRoads || []).filter(r => !r.isAlley);
    
    // For each alley, determine its distance from streets
    const alleyStreetDistances = new Map();
    for (const alley of alleys) {
      let minDist = Infinity;
      for (const pt of alley) {
        for (const street of streets) {
          for (let j = 0; j < street.length - 1; j++) {
            const dist = this.model.pointToSegmentDistance(pt, street[j], street[j + 1]);
            if (dist < minDist) minDist = dist;
          }
        }
      }
      alleyStreetDistances.set(alley, minDist);
    }
    
    // Use lots-mode tessellation for the entire ward instead of strips along alleys
    const shrunkBlock = this.shrinkPolygon(wardShape, 2);
    const allBuildings = this.createAlleysAvoidingPaths(shrunkBlock, 10, 0.12, 0.3, Random.chance(0.3));
    
    // Filter buildings using hierarchical street/alley proximity
    for (const building of allBuildings) {
      const bCenter = building.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
      bCenter.x /= building.length;
      bCenter.y /= building.length;
      
      // Check distance from alleys
      let tooCloseToAlley = false;
      let minAlleyDist = Infinity;
      let closestAlley = null;
      
      for (const checkAlley of alleys) {
        for (let j = 0; j < checkAlley.length - 1; j++) {
          const dist = this.model.pointToSegmentDistance(bCenter, checkAlley[j], checkAlley[j + 1]);
          if (dist < minAlleyDist) {
            minAlleyDist = dist;
            closestAlley = checkAlley;
          }
          if (dist < alleyWidth * 1.2) {
            tooCloseToAlley = true;
            break;
          }
        }
        if (tooCloseToAlley) break;
      }
      
      // Check distance from streets
      let tooCloseToStreet = false;
      let minStreetDistFromBuilding = Infinity;
      
      for (const street of streets) {
        for (let j = 0; j < street.length - 1; j++) {
          const dist = this.model.pointToSegmentDistance(bCenter, street[j], street[j + 1]);
          if (dist < minStreetDistFromBuilding) minStreetDistFromBuilding = dist;
          if (dist < alleyWidth * 2.0) {
            tooCloseToStreet = true;
            break;
          }
        }
        if (tooCloseToStreet) break;
      }
      
      if (tooCloseToAlley || tooCloseToStreet || !this.pointInPolygon(bCenter, wardShape)) {
        continue;
      }
      
      // Apply hierarchical street proximity filtering
      // Priority 1: Near streets (primary - highest density)
      // Priority 2: Near alleys that are close to streets (secondary - medium density)
      // Priority 3: Near alleys far from streets (tertiary - lowest density)
      
      const streetThreshold = alleyWidth * 15;
      let placementProbability = 0;
      
      // Priority 1: Building is near a street directly
      if (minStreetDistFromBuilding < streetThreshold) {
        const streetProximity = 1 - (minStreetDistFromBuilding / streetThreshold);
        placementProbability = Math.pow(streetProximity, 0.3) * 0.8;
      }
      // Priority 2 & 3: Building is near an alley
      else if (closestAlley && minAlleyDist < alleyWidth * 8) {
        // Find how close this alley is to streets
        const alleyDistFromStreet = alleyStreetDistances.get(closestAlley) || Infinity;
        
        if (alleyDistFromStreet < alleyWidth * 20) {
          // Priority 2: Alley is close to streets
          const alleyStreetProximity = 1 - Math.min(1, alleyDistFromStreet / (alleyWidth * 20));
          const alleyProximity = 1 - (minAlleyDist / (alleyWidth * 8));
          placementProbability = Math.pow(alleyStreetProximity, 0.5) * alleyProximity * 0.5;
        } else {
          // Priority 3: Alley is far from streets
          const alleyProximity = 1 - (minAlleyDist / (alleyWidth * 8));
          placementProbability = alleyProximity * 0.2;
        }
      }
      
      // Apply sparse placement multiplier
      if (Random.float() < placementProbability * 0.4) {
        buildings.push(building);
      }
    }
    
    return buildings;
  }
  
  pointNearPolygon(pt, poly, threshold) {
    // Check if point is within threshold distance of polygon
    for (let i = 0; i < poly.length; i++) {
      const p0 = poly[i];
      const p1 = poly[(i + 1) % poly.length];
      const dist = this.model.pointToSegmentDistance(pt, p0, p1);
      if (dist < threshold) return true;
    }
    return false;
  }
  
  pointInPolygon(pt, poly) {
    // Ray casting algorithm to check if point is inside polygon
    let inside = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const xi = poly[i].x, yi = poly[i].y;
      const xj = poly[j].x, yj = poly[j].y;
      
      const intersect = ((yi > pt.y) !== (yj > pt.y))
        && (pt.x < (xj - xi) * (pt.y - yi) / (yj - yi) + xi);
      if (intersect) inside = !inside;
    }
    return inside;
  }
  
  createAlleysRespectingNetwork(polygon, minSq, gridChaos, sizeChaos, split, alleys, depth = 0) {
    // Don't place buildings where alleys are - use modified createAlleys that checks alleys
    return this.createAlleysAvoidingPaths(polygon, minSq, gridChaos, sizeChaos, split, alleys, 0);
  }
  
  createAlleysAvoidingPaths(polygon, minSq, gridChaos, sizeChaos, split, alleyPaths, depth = 0) {
    const maxDepth = StateManager.lotsMode ? 12 : 10;
    const area0 = this.polygonArea(polygon);
    if (!polygon || polygon.length < 3 || area0 <= 0.001 || depth >= maxDepth) {
      // Before accepting as building, check it doesn't overlap alleys
      if (area0 > 0 && alleyPaths && alleyPaths.length > 0) {
        const center = polygon.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
        center.x /= polygon.length;
        center.y /= polygon.length;
        
        // Check if building center is too close to any alley
        const alleyThreshold = (this.model.alleyWidth || 1.8) * 1.5;
        for (const alley of alleyPaths) {
          for (let i = 0; i < alley.length - 1; i++) {
            const dist = this.model.pointToSegmentDistance(center, alley[i], alley[i + 1]);
            if (dist < alleyThreshold) {
              return []; // Skip this building - too close to alley
            }
          }
        }
      }
      return area0 > 0 ? [polygon] : [];
    }
    
    // Find longest edge and split (same as createAlleys)
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
    
    const spread = 0.8 * gridChaos;
    const ratio = (1 - spread) / 2 + Random.float() * spread;
    const angleSpread = Math.PI / 6 * gridChaos;
    const angleOffset = (Random.float() - 0.5) * angleSpread;
    
    const splitX = v0.x + (v1.x - v0.x) * ratio;
    const splitY = v0.y + (v1.y - v0.y) * ratio;
    
    const dx = v1.x - v0.x;
    const dy = v1.y - v0.y;
    const len = Math.sqrt(dx * dx + dy * dy);
    if (len < 0.1) return [];
    
    const nx = dx / len;
    const ny = dy / len;
    const perpX = -ny * Math.cos(angleOffset) - nx * Math.sin(angleOffset);
    const perpY = nx * Math.cos(angleOffset) - ny * Math.sin(angleOffset);
    
    const alleyWidth = split ? (this.model.alleyWidth || 0.6) : 0;
    const cutP1 = new Point(splitX, splitY);
    const cutP2 = new Point(splitX + perpX * 1000, splitY + perpY * 1000);
    
    const halves = this.cutPolygon(polygon, cutP1, cutP2, alleyWidth);
    if (!halves || halves.length < 2) {
      if (area0 < minSq) {
        // Check alley proximity before accepting
        const center = polygon.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
        center.x /= polygon.length;
        center.y /= polygon.length;
        const alleyThreshold = (this.model.alleyWidth || 1.8) * 1.5;
        if (alleyPaths) {
          for (const alley of alleyPaths) {
            for (let i = 0; i < alley.length - 1; i++) {
              const dist = this.model.pointToSegmentDistance(center, alley[i], alley[i + 1]);
              if (dist < alleyThreshold) return [];
            }
          }
        }
        return [polygon];
      }
      const center = polygon.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
      center.x/=polygon.length; center.y/=polygon.length;
      const shrunk = polygon.map(p=>new Point(center.x+(p.x-center.x)*0.98, center.y+(p.y-center.y)*0.98));
      return [shrunk];
    }
    
    const buildings = [];
    for (const half of halves) {
      const area = this.polygonArea(half);
      const sizeVariation = Math.pow(2, 4 * sizeChaos * (Random.float() - 0.5));
      if (area < minSq * sizeVariation) {
        const skipChance = StateManager.lotsMode ? 0.0 : 0.04;
        if (Random.float() > skipChance) {
          // Check alley before adding
          const center = half.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
          center.x /= half.length;
          center.y /= half.length;
          const alleyThreshold = (this.model.alleyWidth || 1.8) * 1.5;
          let tooClose = false;
          if (alleyPaths) {
            for (const alley of alleyPaths) {
              for (let i = 0; i < alley.length - 1; i++) {
                const dist = this.model.pointToSegmentDistance(center, alley[i], alley[i + 1]);
                if (dist < alleyThreshold) {
                  tooClose = true;
                  break;
                }
              }
              if (tooClose) break;
            }
          }
          if (!tooClose) buildings.push(half);
        }
      } else {
        const shouldSplit = StateManager.lotsMode ? (area > minSq * 1.25) : (area > minSq / (Random.float() * Random.float()));
        if (shouldSplit) {
          buildings.push(...this.createAlleysAvoidingPaths(half, minSq, gridChaos, sizeChaos, shouldSplit, alleyPaths, depth + 1));
        } else {
          // Check alley before adding
          const center = half.reduce((a,p)=>({x:a.x+p.x,y:a.y+p.y}),{x:0,y:0});
          center.x /= half.length;
          center.y /= half.length;
          const alleyThreshold = (this.model.alleyWidth || 1.8) * 1.5;
          let tooClose = false;
          if (alleyPaths) {
            for (const alley of alleyPaths) {
              for (let i = 0; i < alley.length - 1; i++) {
                const dist = this.model.pointToSegmentDistance(center, alley[i], alley[i + 1]);
                if (dist < alleyThreshold) {
                  tooClose = true;
                  break;
                }
              }
              if (tooClose) break;
            }
          }
          if (!tooClose) buildings.push(half);
        }
      }
    }
    
    return buildings;
  }

  shrinkPolygonImpl(poly, amount) {
    // Slum: percentage-based shrinking
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
    
    // Subtract water from farm area so no geometry ends up over water
    let land = this.shape;
    if (Array.isArray(this.model.waterBodies) && this.model.waterBodies.length > 0) {
      for (const w of this.model.waterBodies) {
        if (w && w.length >= 3) {
          const clipped = this.subtractPolygon(land, w);
          if (clipped && clipped.length >= 3) land = clipped;
        }
      }
    }
    this.availableShape = land;
    
    // Small farmhouse building
    const center = land.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
    center.x /= land.length;
    center.y /= land.length;
    
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
    
    // Clip housing against water-removed land polygon
    let housingClipped = housing;
    if (land && land.length >= 3) {
      // Ensure house stays within land bounds by intersecting via clipInside semantics
      // Reuse subtractPolygon by subtracting outside-of-land via iterative edge clipping
      // Here simply discard if centroid not inside land
      const inside = (pt, poly)=>{
        let inside=false; for(let i=0,j=poly.length-1;i<poly.length;j=i++){
          const xi=poly[i].x, yi=poly[i].y, xj=poly[j].x, yj=poly[j].y;
          const inter=((yi>pt.y)!=(yj>pt.y)) && (pt.x < (xj-xi)*(pt.y-yi)/(yj-yi)+xi); if(inter) inside=!inside;
        }
        return inside;
      };
      const hc = {x:(housing[0].x+housing[1].x+housing[2].x+housing[3].x)/4,y:(housing[0].y+housing[1].y+housing[2].y+housing[3].y)/4};
      if (!inside(hc, land)) {
        // Move housing towards centre
        const dx=center.x-hc.x, dy=center.y-hc.y; housingClipped = housing.map(p=>new Point(p.x+dx*0.5, p.y+dy*0.5));
      }
    }
    this.buildings = [housingClipped];
    this.geometry = [housingClipped];
    
    // Create subplot (the whole farm field)
    this.subPlots = [land];
    
    // Generate furrows (plowed lines) across the farm
    if (Random.chance(0.7)) { // 70% chance of furrows
      const bounds = (function(poly){
        let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity; for(const p of poly){minX=Math.min(minX,p.x);minY=Math.min(minY,p.y);maxX=Math.max(maxX,p.x);maxY=Math.max(maxY,p.y);} return {x:minX,y:minY,width:maxX-minX,height:maxY-minY};
      })(land);
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
    
    // Water generation - URL overrides if provided
    // coast: 1 forces coast, 0 disables, otherwise ~40% chance
    this.coastNeeded = (StateManager.coast === 1) ? true : (StateManager.coast === 0 ? false : Random.chance(0.4));
    // Support dual river+canal mode
    this.riverType = StateManager.riverType || 'none';
    this.riverNeeded = StateManager.river === 1;
    this.canalNeeded = StateManager.canal === 1;
    
    this.patches = [];
    this.inner = [];
    this.streets = [];
    this.gates = [];
    this.bridges = [];
    
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
    // Build DCEL after walls are finalized so edge types use final membership
    this.buildDCEL();
    // Optional river and/or canal (can have both)
    if (this.riverNeeded) {
      this.riverType = 'river';
      this.buildRiver();
    }
    if (this.canalNeeded) {
      this.riverType = 'canal';
      this.buildRiver();
    }
    // Restore combined type for rendering
    if (this.riverNeeded && this.canalNeeded) {
      this.riverType = 'both';
    } else if (this.riverNeeded) {
      this.riverType = 'river';
    } else if (this.canalNeeded) {
      this.riverType = 'canal';
    }
    // Water affects edge topology; tag edges that cross water as WATER
    if (this.riverNeeded || this.canalNeeded) {
      this.markWaterEdgesFromBodies();
    }
    this.buildStreets();
    this.createWards();
    this.buildGeometry();
    // Add exterior, road-hugging settlements outside the walls
    this.buildOutsideSettlements();
    // Generate named districts for region labels
    this.generateDistricts();
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
    
    // Apply Lloyd's relaxation to all interior points (excluding frame boundary points)
    for (let i = 0; i < VORONOI_RELAXATION_ITERATIONS; i++) {
      const toRelax = voronoi.points.filter(p => !voronoi.frame.includes(p));
      voronoi = Voronoi.relax(voronoi, toRelax);
    }
    
    // Apply Urquhart graph filtering if enabled (removes longest edge from each triangle)
    if (APPLY_URQUHART_GRAPH) {
      voronoi.applyUrquhartGraph();
    }
    
    voronoi.points.sort((p1, p2) => MathUtils.sign(p1.length - p2.length));
    
    const regions = voronoi.partitioning();
    
    // Create patches from regions and apply Chaikin smoothing to cell shapes
    for (const r of regions) {
      const patch = Patch.fromRegion(r);
      // Apply Chaikin smoothing to make Voronoi cells more organic
      if (patch.shape && patch.shape.length >= 3 && CHAIKIN_SMOOTHING_ITERATIONS > 0) {
        patch.shape = Polygon.chaikin(patch.shape, true, CHAIKIN_SMOOTHING_ITERATIONS);
      }
      this.patches.push(patch);
    }
    
    // Calculate initial city radius for water generation
    let tempRadius = 0;
    for (let i = 0; i < Math.min(this.nPatches, this.patches.length); i++) {
      const patch = this.patches[i];
      for (const p of patch.shape) {
        const d = p.length();
        if (d > tempRadius) tempRadius = d;
      }
    }
    this.cityRadius = tempRadius;
    
    // Mark waterbody cells BEFORE city assignment
    if (this.coastNeeded) {
      this.markWaterCells();
    }
    
    const waterCount = this.patches.filter(p => p.waterbody).length;
    // Key metric: waterbodies count (suppressed verbose details)
    console.log('Waterbodies:', waterCount);
    
    // Now assign city roles to patches (excluding waterbodies)
    let count = 0;
    for (const patch of this.patches) {
      // Skip waterbody patches for city roles
      if (patch.waterbody) continue;
      
      if (count === 0) {
        this.center = patch.shape.reduce((min, p) => {
          const minDist = min.x * min.x + min.y * min.y;
          const pDist = p.x * p.x + p.y * p.y;
          return pDist < minDist ? p : min;
        });
        
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
    
    // Recalculate city radius from actual inner patches
    this.cityRadius = 0;
    for (const patch of this.inner) {
      for (const p of patch.shape) {
        const d = p.length();
        if (d > this.cityRadius) this.cityRadius = d;
      }
    }
    
    // Extract water body polygons from waterbody cells for rendering
    this.extractWaterBodies();
    
    // Generate named districts after patches are assigned
    this.generateDistricts();

    // DCEL will be built after patches are known and withinCity flags set
  }

  // --- DCEL construction & edge tagging ---
  buildDCEL() {
    // Build a DCEL face for each patch and half-edges for its boundary
    const roundKey = (p) => `${Math.round(p.x * 1e3)}/${Math.round(p.y * 1e3)}`;
    const segKey = (a, b) => `${roundKey(a)}->${roundKey(b)}`;
    const vertexMap = new Map();
    const getVertex = (p) => {
      const k = roundKey(p);
      let v = vertexMap.get(k);
      if (!v) { v = new DCELVertex(p); vertexMap.set(k, v); }
      return v;
    };

    const edgeMap = new Map(); // map of reversed keys to half-edge for twin linking
    let faceId = 0;
    this.faces = [];

    for (const patch of this.patches) {
      const face = new DCELFace(faceId++);
      face.patch = patch;
      patch.face = face;

      const pts = patch.shape;
      const n = pts.length;
      let firstEdge = null;
      let prev = null;

      for (let i = 0; i < n; i++) {
        const a = pts[i];
        const b = pts[(i + 1) % n];
        const he = new DCELHalfEdge();
        he.origin = getVertex(a);
        he.face = face;
        if (!firstEdge) firstEdge = he;
        if (prev) { prev.next = he; he.prev = prev; }

        // twin linking
        const kFwd = segKey(a, b);
        const kRev = segKey(b, a);
        const rev = edgeMap.get(kFwd); // if an opposite was stored earlier
        if (rev) {
          he.twin = rev; rev.twin = he;
          edgeMap.delete(kFwd);
        } else {
          edgeMap.set(kRev, he);
        }

        prev = he;
      }

      // close the loop
      if (prev && firstEdge) { prev.next = firstEdge; firstEdge.prev = prev; }
      face.edge = firstEdge;
      this.faces.push(face);
    }

    // Tag WALL/WATER edges using membership of neighbouring faces
    const innerSet = new Set(this.patches.filter(p => p.withinCity).map(p => p.face));
    const waterSet = new Set(this.patches.filter(p => p.waterbody).map(p => p.face));
    for (const face of this.faces) {
      for (const e of face.edges()) {
        const twinFace = e.twin ? e.twin.face : null;
        if (!innerSet.has(face)) continue; // only care for city cells
        if (!twinFace || !innerSet.has(twinFace)) {
          e.data = EdgeType.WALL; // city boundary
        } else if (waterSet.has(twinFace)) {
          e.data = EdgeType.WATER;
        }
      }
    }

    // Further mark WATER edges by checking intersection with explicit water polygons (coast or rivers)
    this.markWaterEdgesFromBodies();
  }

  // Tag DCEL edges as WATER if they intersect any polygon in this.waterBodies
  markWaterEdgesFromBodies() {
    if (!this.waterBodies || this.waterBodies.length === 0 || !this.faces) return;
    for (const face of this.faces) {
      if (!face.patch || !face.patch.withinCity) continue;
      for (const e of face.edges()) {
        if (e.data === EdgeType.WALL) continue; // keep boundary type
        const [a, b] = e.asSegment();
        for (const poly of this.waterBodies) {
          if (segmentIntersectsPolygon(a, b, poly)) {
            e.data = EdgeType.WATER;
            break;
          }
        }
      }
    }
  }
  
  /**
   * Mark cells as waterbodies using Perlin noise and distance field
   * 
   */
  markWaterCells() {
    // Simple fractal noise function
    const noise = (x, y) => {
      let value = 0;
      let amplitude = 1;
      let frequency = 1;
      
      for (let i = 0; i < 4; i++) {
        const nx = x * frequency;
        const ny = y * frequency;
        
        // Simple pseudo-random noise based on position
        const n = Math.sin(nx * 12.9898 + ny * 78.233) * 43758.5453;
        value += (n - Math.floor(n)) * amplitude;
        
        amplitude *= 0.5;
        frequency *= 2;
      }
      
      return value;
    };
    
    const bounds = this.cityRadius * 1.5;
    
    // Random rotation for water orientation
    const angle = Random.float() * Math.PI * 2;
    const cos_a = Math.cos(angle);
    const sin_a = Math.sin(angle);
    
    // Vary coastline size dramatically: small (1-2 patches) to huge (8-15+ patches)
    // Use power distribution to favor variety: small, medium, large, and occasional HUGE
    const sizeRoll = Random.float();
    let waterRadius;
    if (sizeRoll < 0.3) {
      // Small: 1-3 patches
      waterRadius = this.cityRadius * (0.15 + Random.float() * 0.25);
    } else if (sizeRoll < 0.6) {
      // Medium: 3-6 patches
      waterRadius = this.cityRadius * (0.4 + Random.float() * 0.3);
    } else if (sizeRoll < 0.85) {
      // Large: 6-10 patches
      waterRadius = this.cityRadius * (0.7 + Random.float() * 0.4);
    } else {
      // HUGE: 10-20+ patches (massive coastline)
      waterRadius = this.cityRadius * (1.1 + Random.float() * 0.6);
    }
    
    const waterOffsetDist = this.cityRadius * (0.3 + Random.float() * 0.4);
    const waterCenter = new Point(
      Math.cos(angle) * waterOffsetDist,
      Math.sin(angle) * waterOffsetDist
    );
    
    // Mark cells as waterbodies based on distance and noise
    for (const patch of this.patches) {
      const center = Polygon.centroid(patch.shape);
      
      // Rotate point
      const rotated = new Point(
        center.x * cos_a - center.y * sin_a,
        center.y * cos_a + center.x * sin_a
      );
      
      // Distance from water center
      let dist = Point.distance(waterCenter, rotated) - waterRadius;
      
      // Adjust for elliptical shape (wider on x if rotated.x > waterCenter.x)
      if (rotated.x > waterCenter.x) {
        dist = Math.min(dist, Math.abs(rotated.y - waterCenter.y) - waterRadius);
      }
      
      // Add noise perturbation for organic edges
      const noiseScale = (rotated.x + bounds) / (2 * bounds);
      const noiseValue = noise(noiseScale, (rotated.y + bounds) / (2 * bounds));
      const noisePerturbation = noiseValue * waterRadius * Math.sqrt(rotated.length() / bounds);
      
      // Mark as waterbody if within perturbed distance
      if (dist + noisePerturbation < 0) {
        patch.waterbody = true;
      }
    }
  }
  
  /**
   * Extract water body polygons from waterbody cells
   * Creates the circumference of all connected waterbody cells
   */
  extractWaterBodies() {
    this.waterBodies = [];
    this.waterBodyTypes = [];
    
    if (!this.coastNeeded) return;
    
    // Find all waterbody patches
    const waterPatches = this.patches.filter(p => p.waterbody);
    if (waterPatches.length === 0) return;
    
    // Find outer edges of water region (edges not shared with other water cells)
    const waterEdges = [];
    
    for (const patch of waterPatches) {
      for (let i = 0; i < patch.shape.length; i++) {
        const a = patch.shape[i];
        const b = patch.shape[(i + 1) % patch.shape.length];
        
        // Check if this edge is shared with another waterbody patch
        let isShared = false;
        for (const otherPatch of waterPatches) {
          if (otherPatch === patch) continue;
          
          // Check if the reverse edge exists in other patch
          if (Polygon.findEdge(otherPatch.shape, b, a) !== -1) {
            isShared = true;
            break;
          }
        }
        
        if (!isShared) {
          waterEdges.push({a, b});
        }
      }
    }
    
    // Chain edges together to form water boundary polygon(s)
    if (waterEdges.length > 0) {
      const waterPoly = [];
      const used = new Set();
      let current = waterEdges[0];
      let index = 0;
      used.add(index);
      
      waterPoly.push(current.a);
      
      // Chain edges
      let iterations = 0;
      const maxIterations = waterEdges.length + 10;
      
      while (iterations < maxIterations) {
        waterPoly.push(current.b);
        
        // Find next edge that starts where this one ends
        let found = false;
        for (let i = 0; i < waterEdges.length; i++) {
          if (used.has(i)) continue;
          
          const edge = waterEdges[i];
          if (Point.distance(current.b, edge.a) < 0.1) {
            current = edge;
            index = i;
            used.add(i);
            found = true;
            break;
          }
        }
        
        if (!found || Point.distance(current.b, waterPoly[0]) < 0.1) break;
        iterations++;
      }
      
      if (waterPoly.length >= 3) {
        // Heavily smooth coastline to remove ALL sharp Voronoi corners (3-5 passes for very organic look)
        const smoothPasses = POLYGON_SMOOTHING_PASSES + Random.int(0, 3);
        const smoothedCoast = Polygon.smooth(waterPoly, null, smoothPasses);
        this.waterBodies.push(smoothedCoast);
        this.waterBodyTypes.push('coast');
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

  getPolygonCenter(polygon) {
    let cx = 0, cy = 0;
    for (const p of polygon) {
      cx += p.x;
      cy += p.y;
    }
    return new Point(cx / polygon.length, cy / polygon.length);
  }
  
  getPolygonRadius(polygon) {
    const center = this.getPolygonCenter(polygon);
    let maxDist = 0;
    for (const p of polygon) {
      const dist = Point.distance(p, center, 'getPolygonRadius');
      if (dist > maxDist) maxDist = dist;
    }
    return maxDist;
  }

  buildWalls() {
    if (this.inner.length === 0) {
      this.borderShape = [];
      return;
    }
    
    if (this.inner.length === 1) {
      this.borderShape = [...this.inner[0].shape];
      // Filter out any invalid vertices
      this.borderShape = this.borderShape.filter(v => v && v.x !== undefined && v.y !== undefined);
      return;
    }
    
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
    
    // Recompute city membership robustly: centroid-inside test
    if (this.borderShape.length > 0) {
      // Ensure border has only valid points
      this.borderShape = this.borderShape.filter(v => v && v.x !== undefined && v.y !== undefined);
      for (const patch of this.patches) {
        const centroid = Polygon.centroid(patch.shape);
        patch.withinCity = this.isPointInPolygon(centroid, this.borderShape) && !patch.waterbody;
      }
      // Refresh inner list
      this.inner = this.patches.filter(p => p.withinCity);
    }
    
    
    // Generate gates
    if (this.wallsNeeded && this.borderShape.length > 0) {
      const numGates = 2 + Random.int(0, 3);
      const validBorder = this.borderShape.filter(v => v && v.x !== undefined && v.y !== undefined);
      for (let i = 0; i < numGates; i++) {
        if (validBorder.length === 0) break;
        const idx = Random.int(0, validBorder.length);
        this.gates.push(validBorder[idx]);
      }
      
      // Apply smoothing to wall shape, preserving gate positions AND water edge vertices
      const excludePoints = [...this.gates];
      
      // Add water edge vertices to exclusion list 
      if (this.waterBodies && this.waterBodies.length > 0) {
        for (const waterBody of this.waterBodies) {
          for (const point of waterBody) {
            excludePoints.push(point);
          }
        }
      }
      
      this.borderShape = Polygon.smooth(this.borderShape, excludePoints, POLYGON_SMOOTHING_PASSES);
      // Post-smooth validation
      this.borderShape = this.borderShape.filter(v => v && v.x !== undefined && v.y !== undefined);
      // Keep gates valid too
      this.gates = this.gates.filter(g => g && g.x !== undefined && g.y !== undefined);
    }
    
    // Store wall edges as pairs of consecutive vertices
    // This allows wards to identify which edges are wall edges
    this.wallEdges = [];
    for (let i = 0; i < this.borderShape.length; i++) {
      const v1 = this.borderShape[i];
      const v2 = this.borderShape[(i + 1) % this.borderShape.length];
      this.wallEdges.push([v1, v2]);
    }
    
    // Filter patches to reasonable radius - keep patches within 3x city radius
    const radius = this.cityRadius;
    const maxDist = radius * 3;
    // Debug (suppressed): filtering patches by radius
    this.patches = this.patches.filter(p => {
      const patchCenter = Polygon.centroid(p.shape);
      const dist = Point.distance(patchCenter, this.center, 'buildWalls/radiusFilter');
      return dist < maxDist;
    });
    
    // Debug (suppressed): after radius filter count
  }

  // Build a river/canal polygon crossing the city; add to waterBodies/waterBodyTypes
  buildRiver() {
    // Create a path across ENTIRE map canvas, not just city limits
    // Use a large multiplier to ensure river extends beyond any reasonable viewport
    const R = this.cityRadius * 6.0; // Span entire map area
    const angle = Random.float() * Math.PI; // random orientation
    const dir = new Point(Math.cos(angle), Math.sin(angle));
    const start = new Point(dir.x * -R, dir.y * -R);
    const end = new Point(dir.x * R, dir.y * R);

    let path = [];
    if (this.riverType === 'canal') {
      // Mostly straight canal with slight jitter near center
      const offset = (Random.float() - 0.5) * this.cityRadius * 0.1;
      const ortho = new Point(-dir.y, dir.x);
      const mid1 = new Point(start.x + (end.x - start.x) * 0.33 + ortho.x * offset, start.y + (end.y - start.y) * 0.33 + ortho.y * offset);
      const mid2 = new Point(start.x + (end.x - start.x) * 0.66 - ortho.x * offset, start.y + (end.y - start.y) * 0.66 - ortho.y * offset);
      path = [start, mid1, mid2, end];
    } else {
      // VERY BENDY meandering river: Many segments with aggressive multi-frequency sinusoidal lateral offsets
      const segments = 24; // More segments = more curves
      const ortho = new Point(-dir.y, dir.x);
      const amp = this.cityRadius * 0.25; // Much larger amplitude for dramatic bends
      const meanderIntensity = StateManager.riverMeander || 0.5; // 0-1 scale
      
      // Value noise for micro-meanders (seeded pseudo-random)
      const valueNoise = (x) => {
        const n = Math.sin(x * 127.1 + Random.seed * 0.0001) * Math.cos(x * 311.7 + Random.seed * 0.0002);
        return (n - Math.floor(n)) - 0.5; // -0.5 to 0.5
      };
      
      for (let i = 0; i <= segments; i++) {
        const t = i / segments;
        const baseX = start.x + (end.x - start.x) * t;
        const baseY = start.y + (end.y - start.y) * t;
        // Multi-frequency sine waves with MUCH MORE aggressive bending
        const sineWobble = amp * (
          Math.sin(t * Math.PI * 3.5) * 1.0 +          // Primary meander
          Math.sin(t * Math.PI * 6.2 + 1.3) * 0.6 +    // Secondary curves
          Math.sin(t * Math.PI * 1.8 + 2.7) * 0.8      // Tertiary variation
        ) * (0.5 + 0.5 * Math.sin(t * Math.PI));       // Modulation envelope
        
        // Micro-meanders: layered value noise at different scales
        const microMeander = meanderIntensity * amp * 0.3 * (
          valueNoise(t * 15.7) * 0.6 +                 // Fine detail
          valueNoise(t * 8.3 + 2.1) * 0.4 +            // Medium detail
          valueNoise(t * 4.1 + 4.7) * 0.3              // Coarse oxbow swells
        );
        
        const wobble = sineWobble + microMeander;
        path.push(new Point(baseX + ortho.x * wobble, baseY + ortho.y * wobble));
      }
      // Smooth path multiple times for natural curves (open polyline)
      path = Polygon.smoothOpen(path, null, 2);
    }
    
    // Safety check
    if (!path || path.length < 2) {
      console.error('River path generation failed');
      return;
    }

    // Thicken path into a polygon strip
    const baseW = this.riverType === 'canal' ? Math.max(8, StateManager.streetWidth * 2) : Math.max(10, StateManager.streetWidth * 3);
    const left = [];
    const right = [];
    // Precompute width noise phases for coherent variation
    const phase1 = Random.float() * Math.PI * 2;
    const phase2 = Random.float() * Math.PI * 2;
    const phase3 = Random.float() * Math.PI * 2;
    
    for (let i = 0; i < path.length - 1; i++) {
      const a = path[i];
      const b = path[i + 1];
      // Comprehensive null/undefined checks
      if (!a || !b || a.x === undefined || a.y === undefined || b.x === undefined || b.y === undefined) {
        console.warn('Invalid path point at index', i, 'a:', a, 'b:', b);
        continue;
      }
      const dx = b.x - a.x, dy = b.y - a.y;
      const len = Math.hypot(dx, dy) || 1e-6;
      const nx = -dy / len, ny = dx / len; // left normal
      // Width varies strongly along a natural river; canals stay uniform
      const t = i / Math.max(1, path.length - 1);
      let vary = 1;
      if (this.riverType !== 'canal') {
        // Multi-frequency width noise with stronger amplitude
        const n = (
          0.9 +
          0.6 * Math.sin(t * Math.PI * 4.2 + phase1) +
          0.35 * Math.sin(t * Math.PI * 8.7 + phase2) +
          0.25 * Math.sin(t * Math.PI * 13.1 + phase3)
        );
        
        // Value noise for oxbow swell width balloons
        const meanderIntensity = StateManager.riverMeander || 0.5;
        const valueNoise = (x) => {
          const n = Math.sin(x * 127.1 + Random.seed * 0.0001) * Math.cos(x * 311.7 + Random.seed * 0.0002);
          return (n - Math.floor(n)) - 0.5; // -0.5 to 0.5
        };
        const widthSwell = meanderIntensity * 0.4 * (
          valueNoise(t * 6.3 + 1.2) +                  // Occasional wide pools
          valueNoise(t * 11.7 + 3.8) * 0.5             // Finer width variation
        );
        
        vary = Math.max(0.5, n + widthSwell); // keep from collapsing too thin
      }
      // Taper towards ends (ease in/out) for rivers to avoid hard cut at map edge
      const taper = (this.riverType === 'canal') ? 1 : Math.max(0.25, Math.sin(Math.PI * t));
      const width = baseW * vary * taper;
      left.push(new Point(a.x + nx * width, a.y + ny * width));
      right.push(new Point(a.x - nx * width, a.y - ny * width));
      if (i === path.length - 2) {
        left.push(new Point(b.x + nx * width, b.y + ny * width));
        right.push(new Point(b.x - nx * width, b.y - ny * width));
      }
    }
    
    // Ensure we have valid polygons
    if (left.length < 2 || right.length < 2) {
      console.error('Failed to generate river polygon - insufficient points');
      return;
    }
    
    let waterPoly = [...left, ...right.reverse()];

    if (!this.waterBodies) this.waterBodies = [];
    if (!this.waterBodyTypes) this.waterBodyTypes = [];
    // Heavily smooth for very organic look without ANY sharp corners (5-7 passes for rivers, 2 for canals)
    const smoothPasses = this.riverType === 'canal' ? 2 : (POLYGON_SMOOTHING_PASSES + 2 + Random.int(0, 3));
    const result = Polygon.smooth(waterPoly, null, smoothPasses);
    
    // Key metric: river/canal polygon built
    console.log('Water polygon built:', this.riverType, 'points:', waterPoly.length, 'smoothPasses:', smoothPasses);
    
    this.waterBodies.push(result);
    this.waterBodyTypes.push(this.riverType);
  }

  buildStreets() {
    // Build topology graph for pathfinding - ONLY from non-waterbody patches
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
        if (vertex && vertex.x !== undefined && vertex.y !== undefined) {
          targetVertices.push(vertex);
        }
      }
      
      // Sort by distance to center and take closest ones
      targetVertices.sort((a, b) => {
        const distA = Point.distance(a, center, 'buildStreets/sortA');
        const distB = Point.distance(b, center, 'buildStreets/sortB');
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
        let minDist = Point.distance(virtualGate, nearest, 'buildStreets/snapVirtual/minInit');
        
        for (const borderVertex of this.borderShape) {
          const dist = Point.distance(virtualGate, borderVertex, 'buildStreets/snapVirtual/scan');
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
      if (!gate || gate.x === undefined || gate.y === undefined) continue;
        let nearestTarget = null;
      let minDist = Infinity;
      
      for (const vertex of targetVertices) {
        if (!vertex || vertex.x === undefined || vertex.y === undefined) continue;
        const dist = Point.distance(gate, vertex, 'buildStreets/nearestTarget');
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
      if (!patch.shape || patch.shape.length < 2) continue;
      for (let i = 0; i < patch.shape.length; i++) {
        const v0 = patch.shape[i];
        const v1 = patch.shape[(i + 1) % patch.shape.length];
        if (!v0 || !v1 || v0.x === undefined || v0.y === undefined || v1.x === undefined || v1.y === undefined) continue;
        
        if (!extendedGraph.has(v0)) extendedGraph.set(v0, {edges: new Map()});
        if (!extendedGraph.has(v1)) extendedGraph.set(v1, {edges: new Map()});
        
        const dist = Point.distance(v0, v1, 'buildStreets/exteriorEdge');
        extendedGraph.get(v0).edges.set(v1, dist);
        extendedGraph.get(v1).edges.set(v0, dist);
      }
    }
    
    // For each gate (real or virtual), pathfind outward to a far point
    for (const gate of roadStartPoints) {
      if (!gate || gate.x === undefined || gate.y === undefined) continue;
      const angle = Math.atan2(gate.y, gate.x);
      const roadLength = this.cityRadius * 1.5;
      
      // Find the farthest vertex in the extended graph along this direction
      let bestTarget = null;
      let maxDist = 0;
      
      for (const vertex of extendedGraph.keys()) {
        if (!vertex || vertex.x === undefined || vertex.y === undefined) continue;
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
          if (!vertex || vertex.x === undefined || vertex.y === undefined) continue;
          const dist = Point.distance(gate, vertex, 'buildStreets/farthestFallback');
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
            if (!point || point.x === undefined || point.y === undefined) continue;
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
    // Optional corner cutting / smoothing (Chaikin) to improve aesthetics
    const smoothPath = (path, iters = 1, keepEnds = true) => {
      let pts = path;
      for (let it = 0; it < iters; it++) {
        if (!pts || pts.length < 3) break;
        const out = [];
        const start = pts[0], end = pts[pts.length - 1];
        if (keepEnds) out.push(start);
        for (let i = 0; i < pts.length - 1; i++) {
          const p = pts[i], q = pts[i + 1];
          const Q = new Point(0.75 * p.x + 0.25 * q.x, 0.75 * p.y + 0.25 * q.y);
          const R = new Point(0.25 * p.x + 0.75 * q.x, 0.25 * p.y + 0.75 * q.y);
          out.push(Q, R);
        }
        if (keepEnds) { out.push(end); } else { out.pop(); }
        pts = out;
      }
      return pts;
    };

    // Smooth interior streets and exterior roads FIRST
    if (Array.isArray(this.streets)) {
      this.streets = this.streets.map(p => smoothPath(p, 1, true));
    }
    if (Array.isArray(this.exteriorRoads)) {
      this.exteriorRoads = this.exteriorRoads.map(p => smoothPath(p, 1, true));
    }
    
    // THEN compute bridges and extend paths (so bridge connections aren't lost to smoothing)
    this.computeBridgesFromPaths();
    // Add forced river crossing if river splits city
    this.ensureRiverCrossing();

    // Add random piers for visual interest
    this.generatePiers();
    // Then tag adjacent DCEL edges as ROAD
    this.markRoadEdgesFromStreets();
  }

  // Compute bridges where streets cross water - ensure bridges ALWAYS touch water edges
  computeBridgesFromPaths() {
    this.bridges = [];
    if (!this.waterBodies || this.waterBodies.length === 0) {
      // No water bodies - no bridges needed
      return;
    }
    const allPaths = [];
    if (Array.isArray(this.streets)) allPaths.push(...this.streets);
    if (Array.isArray(this.exteriorRoads)) allPaths.push(...this.exteriorRoads);
    if (allPaths.length === 0) {
      // No streets/roads to bridge
      return;
    }

    const streetW = (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0;
    const extend = streetW * 0.5;
    const minBridgeSpacing = streetW * 4; // Bridges must be this far apart
    const maxBridgeLength = this.cityRadius ? this.cityRadius * 0.4 : 50; // Reject absurdly long bridges
    
    // Helper: check if point is in ANY water body
    const pointInAnyWater = (p) => {
      for (const poly of this.waterBodies) {
        if (!poly || poly.length < 3) continue;
        let inside = false;
        for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
          const xi = poly[i].x, yi = poly[i].y;
          const xj = poly[j].x, yj = poly[j].y;
          const intersect = ((yi > p.y) !== (yj > p.y)) && (p.x < (xj - xi) * (p.y - yi) / (yj - yi) + xi);
          if (intersect) inside = !inside;
        }
        if (inside) return true;
      }
      return false;
    };
    
    // Helper: check if point is in a SPECIFIC water body
    const pointInWater = (p, poly) => {
      let inside = false;
      for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
        const xi = poly[i].x, yi = poly[i].y;
        const xj = poly[j].x, yj = poly[j].y;
        const intersect = ((yi > p.y) !== (yj > p.y)) && (p.x < (xj - xi) * (p.y - yi) / (yj - yi) + xi);
        if (intersect) inside = !inside;
      }
      return inside;
    };
    
    // Helper: find water boundary crossings
    const findCrossings = (a, b, poly) => {
      const hits = [];
      for (let j = 0; j < poly.length; j++) {
        const c = poly[j], d = poly[(j + 1) % poly.length];
        const r = {x: b.x - a.x, y: b.y - a.y};
        const s = {x: d.x - c.x, y: d.y - c.y};
        const denom = r.x * s.y - r.y * s.x;
        if (Math.abs(denom) < 1e-9) continue;
        const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
        const u = ((c.x - a.x) * r.y - (c.y - a.y) * r.x) / denom;
        if (t >= -0.01 && t <= 1.01 && u >= 0 && u <= 1) {
          hits.push({t: t, point: new Point(a.x + r.x * t, a.y + r.y * t)});
        }
      }
      hits.sort((x, y) => x.t - y.t);
      return hits;
    };
    
    // Helper: check if bridge is too close to existing bridges
    const tooCloseToOthers = (bridgeStart, bridgeEnd) => {
      const midpoint = new Point((bridgeStart.x + bridgeEnd.x) / 2, (bridgeStart.y + bridgeEnd.y) / 2);
      for (const existing of this.bridges) {
        const existingMid = new Point((existing[0].x + existing[1].x) / 2, (existing[0].y + existing[1].y) / 2);
        const dist = Math.hypot(midpoint.x - existingMid.x, midpoint.y - existingMid.y);
        if (dist < minBridgeSpacing) return true;
      }
      return false;
    };
    
    let totalCrossings = 0;
    
    // Helper: get water body type by index
    const getWaterType = (poly) => {
      const idx = this.waterBodies.indexOf(poly);
      const type = (this.waterBodyTypes && idx >= 0 && idx < this.waterBodyTypes.length) 
        ? this.waterBodyTypes[idx] 
        : 'unknown';
      // Debug (suppressed): water body type lookup
      return type;
    };
    
    // For CANALS, find opportunities to connect street endpoints across water FIRST
    // This handles streets that stop at water edges instead of crossing
    for (const waterPoly of this.waterBodies) {
      if (!waterPoly || waterPoly.length < 3) continue;
      
      const waterType = getWaterType(waterPoly);
      if (waterType !== 'canal') continue; // Only for canals initially
      
      // Debug (suppressed): checking canal street-to-street opportunities
      
      const maxConnectionDist = this.cityRadius ? this.cityRadius * 0.25 : 40;
      const connectionSearchDist = streetW * 6; // How far from water to look for street endpoints
      
      // Find all street endpoints near this water body
      const nearbyEndpoints = [];
      
      for (const path of allPaths) {
        if (!path || path.length < 2) continue;
        
        // Check first point
        const first = path[0];
        let minDistFirst = Infinity;
        for (let j = 0; j < waterPoly.length; j++) {
          const a = waterPoly[j];
          const b = waterPoly[(j + 1) % waterPoly.length];
          const t = Math.max(0, Math.min(1, 
            ((first.x - a.x) * (b.x - a.x) + (first.y - a.y) * (b.y - a.y)) / 
            (Math.hypot(b.x - a.x, b.y - a.y) ** 2 || 1)
          ));
          const proj = {x: a.x + t * (b.x - a.x), y: a.y + t * (b.y - a.y)};
          const dist = Math.hypot(proj.x - first.x, proj.y - first.y);
          minDistFirst = Math.min(minDistFirst, dist);
        }
        
        if (minDistFirst < connectionSearchDist) {
          nearbyEndpoints.push({point: first, path: path, isFirst: true});
        }
        
        // Check last point
        const last = path[path.length - 1];
        let minDistLast = Infinity;
        for (let j = 0; j < waterPoly.length; j++) {
          const a = waterPoly[j];
          const b = waterPoly[(j + 1) % waterPoly.length];
          const t = Math.max(0, Math.min(1, 
            ((last.x - a.x) * (b.x - a.x) + (last.y - a.y) * (b.y - a.y)) / 
            (Math.hypot(b.x - a.x, b.y - a.y) ** 2 || 1)
          ));
          const proj = {x: a.x + t * (b.x - a.x), y: a.y + t * (b.y - a.y)};
          const dist = Math.hypot(proj.x - last.x, proj.y - last.y);
          minDistLast = Math.min(minDistLast, dist);
        }
        
        if (minDistLast < connectionSearchDist) {
          nearbyEndpoints.push({point: last, path: path, isFirst: false});
        }
      }
      
      // Debug (suppressed): endpoints near canal
      
      // Try to pair endpoints across water
      for (let i = 0; i < nearbyEndpoints.length; i++) {
        for (let j = i + 1; j < nearbyEndpoints.length; j++) {
          const ep1 = nearbyEndpoints[i];
          const ep2 = nearbyEndpoints[j];
          
          // Don't bridge endpoints from the same path
          if (ep1.path === ep2.path) continue;
          
          const dist = Math.hypot(ep2.point.x - ep1.point.x, ep2.point.y - ep1.point.y);
          if (dist > maxConnectionDist) continue;
          
          // Check if line crosses this water body
          const mid = {x: (ep1.point.x + ep2.point.x) / 2, y: (ep1.point.y + ep2.point.y) / 2};
          if (!pointInWater(mid, waterPoly)) continue;
          
          // Find where the line crosses water edges
          const crossings = findCrossings(ep1.point, ep2.point, waterPoly);
          
          let bridgeStart, bridgeEnd;
          
          if (crossings.length >= 2) {
            // Use water crossing points
            bridgeStart = crossings[0].point;
            bridgeEnd = crossings[crossings.length - 1].point;
          } else {
            // Fallback: use street endpoints directly
            bridgeStart = ep1.point;
            bridgeEnd = ep2.point;
          }
          
          const bridgeLen = Math.hypot(bridgeEnd.x - bridgeStart.x, bridgeEnd.y - bridgeStart.y);
          
          if (bridgeLen <= maxConnectionDist && !tooCloseToOthers(bridgeStart, bridgeEnd)) {
            // Helper to check if point is inside a polygon
            const pointInPolygon = (pt, poly) => {
              let inside = false;
              for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
                const xi = poly[i].x, yi = poly[i].y;
                const xj = poly[j].x, yj = poly[j].y;
                const intersect = ((yi > pt.y) !== (yj > pt.y)) && (pt.x < (xj - xi) * (pt.y - yi) / (yj - yi) + xi);
                if (intersect) inside = !inside;
              }
              return inside;
            };
            
            // Check if bridge would hit any buildings
            let bridgeHitsBuilding = false;
            if (this.patches) {
              const numSamples = 20;
              for (let sample = 0; sample <= numSamples && !bridgeHitsBuilding; sample++) {
                const t = sample / numSamples;
                const testPoint = {
                  x: bridgeStart.x + (bridgeEnd.x - bridgeStart.x) * t,
                  y: bridgeStart.y + (bridgeEnd.y - bridgeStart.y) * t
                };
                
                for (const patch of this.patches) {
                  if (!patch.ward || !patch.ward.geometry) continue;
                  for (const building of patch.ward.geometry) {
                    if (!building || building.length < 3) continue;
                    if (pointInPolygon(testPoint, building)) {
                      bridgeHitsBuilding = true;
                      break;
                    }
                  }
                  if (bridgeHitsBuilding) break;
                }
              }
            }
            
            if (!bridgeHitsBuilding) {
              // Debug (suppressed): canal street-to-street bridge details
              
              this.bridges.push([bridgeStart, bridgeEnd]);
              totalCrossings++;
              
              // Extend streets to bridge endpoints
              if (ep1.isFirst) {
                ep1.path.unshift(bridgeStart);
                ep1.path.unshift(bridgeEnd);
              } else {
                ep1.path.push(bridgeStart);
                ep1.path.push(bridgeEnd);
              }
              
              if (ep2.isFirst) {
                ep2.path.unshift(bridgeEnd);
                ep2.path.unshift(bridgeStart);
              } else {
                ep2.path.push(bridgeEnd);
                ep2.path.push(bridgeStart);
              }
              
              // Debug (suppressed): extended canal bridge paths
            }
          }
        }
      }
    }
    
    // PRIORITY 2: Process paths that already cross water bodies
    let pathsChecked = 0;
    for (const path of allPaths) {
      if (!path || path.length < 2) continue;
      pathsChecked++;
      
      for (const waterPoly of this.waterBodies) {
        if (!waterPoly || waterPoly.length < 3) continue;
        
        const waterType = getWaterType(waterPoly);
        let inWater = false;
        let entryPoint = null;
        let entryDir = null;
        let segmentsChecked = 0;
        let hitsFound = 0;
        
        for (let i = 0; i < path.length - 1; i++) {
          segmentsChecked++;
          const a = path[i];
          const b = path[i + 1];
          if (!a || !b) continue;
          
          const segLen = Math.hypot(b.x - a.x, b.y - a.y) || 1e-6;
          const dir = {x: (b.x - a.x) / segLen, y: (b.y - a.y) / segLen};
          const hits = findCrossings(a, b, waterPoly);
          const aIn = pointInWater(a, waterPoly);
          const bIn = pointInWater(b, waterPoly);
          
          if (!inWater) {
            if (hits.length >= 2) {
              // Crosses in single segment - bridge endpoints are EXACTLY where path crosses water edge
              const entry = hits[0].point;
              const exit = hits[hits.length - 1].point;
              
              let finalEntry = entry;
              let finalExit = exit;
              
              // For CANALS: find perpendicular crossing (shortest straight path across)
              if (waterType === 'canal') {
                console.log('CANAL BRIDGE (single-seg): Entry at', entry, 'Exit at', exit);
                // Find the canal edge closest to the entry point
                let closestEdgeDist = Infinity;
                let closestEdgeStart = null;
                let closestEdgeEnd = null;
                
                for (let j = 0; j < waterPoly.length; j++) {
                  const p1 = waterPoly[j];
                  const p2 = waterPoly[(j + 1) % waterPoly.length];
                  
                  // Distance from entry point to this edge
                  const edgeDx = p2.x - p1.x;
                  const edgeDy = p2.y - p1.y;
                  const edgeLen = Math.hypot(edgeDx, edgeDy) || 1;
                  
                  // Project entry point onto edge
                  const t = Math.max(0, Math.min(1, 
                    ((entry.x - p1.x) * edgeDx + (entry.y - p1.y) * edgeDy) / (edgeLen * edgeLen)
                  ));
                  const projX = p1.x + t * edgeDx;
                  const projY = p1.y + t * edgeDy;
                  const dist = Math.hypot(projX - entry.x, projY - entry.y);
                  
                  if (dist < closestEdgeDist && dist < 2) {
                    closestEdgeDist = dist;
                    closestEdgeStart = p1;
                    closestEdgeEnd = p2;
                  }
                }
                
                if (closestEdgeStart && closestEdgeEnd) {
                  // Calculate edge direction
                  const edgeDx = closestEdgeEnd.x - closestEdgeStart.x;
                  const edgeDy = closestEdgeEnd.y - closestEdgeStart.y;
                  const edgeLen = Math.hypot(edgeDx, edgeDy) || 1;
                  const edgeUnitX = edgeDx / edgeLen;
                  const edgeUnitY = edgeDy / edgeLen;
                  
                  // Perpendicular direction (90 degrees)
                  const perpX = -edgeUnitY;
                  const perpY = edgeUnitX;
                  
                  // Cast ray from entry in perpendicular direction
                  const rayLen = maxBridgeLength * 2;
                  const rayEnd1 = new Point(entry.x + perpX * rayLen, entry.y + perpY * rayLen);
                  const rayEnd2 = new Point(entry.x - perpX * rayLen, entry.y - perpY * rayLen);
                  
                  // Find crossings in both perpendicular directions
                  const crossings1 = findCrossings(entry, rayEnd1, waterPoly);
                  const crossings2 = findCrossings(entry, rayEnd2, waterPoly);
                  
                  // Use the first crossing in either direction (opposite shore)
                  if (crossings1.length > 0 && crossings1[0].t > 0.01) {
                    finalExit = crossings1[0].point;
                    console.log('  Using perpendicular exit (dir1):', finalExit);
                  } else if (crossings2.length > 0 && crossings2[0].t > 0.01) {
                    finalExit = crossings2[0].point;
                    console.log('  Using perpendicular exit (dir2):', finalExit);
                  } else {
                    console.log('  No perpendicular crossing found, keeping original');
                  }
                }
              }
              
              const bridgeLen = Math.hypot(finalExit.x - finalEntry.x, finalExit.y - finalEntry.y);
              
              // Validate this isn't at a water body overlap (check if endpoints are in OTHER water)
              const entryInOtherWater = this.waterBodies.some(w => w !== waterPoly && pointInWater(finalEntry, w));
              const exitInOtherWater = this.waterBodies.some(w => w !== waterPoly && pointInWater(finalExit, w));
              
              if (!entryInOtherWater && !exitInOtherWater && bridgeLen <= maxBridgeLength) {
                if (!tooCloseToOthers(finalEntry, finalExit)) {
                  this.bridges.push([finalEntry, finalExit]);
                  totalCrossings++;
                }
              }
            } else if (hits.length === 1 && !aIn && bIn) {
              entryPoint = hits[0].point;
              entryDir = {x: dir.x, y: dir.y};
              inWater = true;
            }
          } else {
            if (hits.length > 0 || !bIn) {
              const exitPoint = hits.length > 0 ? hits[hits.length - 1].point : a;
              
              let finalEntry = entryPoint;
              let finalExit = exitPoint;
              
              // For CANALS: find perpendicular crossing (shortest straight path across)
              if (waterType === 'canal') {
                console.log('CANAL BRIDGE: Entry at', entryPoint, 'Exit at', exitPoint);
                // Find the two closest canal edges to the entry point
                let closestEdgeDist = Infinity;
                let closestEdgeStart = null;
                let closestEdgeEnd = null;
                
                for (let j = 0; j < waterPoly.length; j++) {
                  const p1 = waterPoly[j];
                  const p2 = waterPoly[(j + 1) % waterPoly.length];
                  
                  // Distance from entry point to this edge
                  const edgeDx = p2.x - p1.x;
                  const edgeDy = p2.y - p1.y;
                  const edgeLen = Math.hypot(edgeDx, edgeDy) || 1;
                  
                  // Project entry point onto edge
                  const t = Math.max(0, Math.min(1, 
                    ((entryPoint.x - p1.x) * edgeDx + (entryPoint.y - p1.y) * edgeDy) / (edgeLen * edgeLen)
                  ));
                  const projX = p1.x + t * edgeDx;
                  const projY = p1.y + t * edgeDy;
                  const dist = Math.hypot(projX - entryPoint.x, projY - entryPoint.y);
                  
                  if (dist < closestEdgeDist && dist < 2) { // Only consider very close edges (on the boundary)
                    closestEdgeDist = dist;
                    closestEdgeStart = p1;
                    closestEdgeEnd = p2;
                  }
                }
                
                if (closestEdgeStart && closestEdgeEnd) {
                  // Calculate edge direction
                  const edgeDx = closestEdgeEnd.x - closestEdgeStart.x;
                  const edgeDy = closestEdgeEnd.y - closestEdgeStart.y;
                  const edgeLen = Math.hypot(edgeDx, edgeDy) || 1;
                  const edgeUnitX = edgeDx / edgeLen;
                  const edgeUnitY = edgeDy / edgeLen;
                  
                  // Perpendicular direction (90 degrees)
                  const perpX = -edgeUnitY;
                  const perpY = edgeUnitX;
                  
                  // Cast ray from entry in perpendicular direction
                  const rayLen = maxBridgeLength * 2;
                  const rayEnd1 = new Point(entryPoint.x + perpX * rayLen, entryPoint.y + perpY * rayLen);
                  const rayEnd2 = new Point(entryPoint.x - perpX * rayLen, entryPoint.y - perpY * rayLen);
                  
                  // Find crossings in both perpendicular directions
                  const crossings1 = findCrossings(entryPoint, rayEnd1, waterPoly);
                  const crossings2 = findCrossings(entryPoint, rayEnd2, waterPoly);
                  
                  // Use the first crossing in either direction (opposite shore)
                  if (crossings1.length > 0 && crossings1[0].t > 0.01) {
                    finalExit = crossings1[0].point;
                    console.log('  Using perpendicular exit (dir1):', finalExit);
                  } else if (crossings2.length > 0 && crossings2[0].t > 0.01) {
                    finalExit = crossings2[0].point;
                    console.log('  Using perpendicular exit (dir2):', finalExit);
                  } else {
                    console.log('  No perpendicular crossing found, keeping original');
                  }
                }
              }
              
              const bridgeLen = Math.hypot(finalExit.x - finalEntry.x, finalExit.y - finalEntry.y);
              
              // Validate not at water overlap and not too long
              const entryInOtherWater = this.waterBodies.some(w => w !== waterPoly && pointInWater(finalEntry, w));
              const exitInOtherWater = this.waterBodies.some(w => w !== waterPoly && pointInWater(finalExit, w));
              
              if (!entryInOtherWater && !exitInOtherWater && bridgeLen <= maxBridgeLength) {
                if (!tooCloseToOthers(finalEntry, finalExit)) {
                  this.bridges.push([finalEntry, finalExit]);
                  totalCrossings++;
                }
              }
              
              inWater = false;
              entryPoint = null;
              entryDir = null;
            }
          }
        }
      }
    }
    
    // ADDITIONAL: Find opportunities to connect streets across water where no path currently crosses
    // Look for street endpoints near water on one side, and other street endpoints near water on opposite side
    const connectionSearchDist = streetW * 3; // How far from water to look for street endpoints
    const maxConnectionDist = maxBridgeLength * 0.8; // Max distance to connect streets
    
    // Debug (suppressed): start street-to-street bridge search
    
    for (const waterPoly of this.waterBodies) {
      if (!waterPoly || waterPoly.length < 3) continue;
      
      // Find all street endpoints near this water body
      const nearbyEndpoints = [];
      // Debug (suppressed): checking water body path counts
      for (const path of allPaths) {
        if (!path || path.length < 2) continue;
        
        // Check first endpoint
        const first = path[0];
        if (!pointInAnyWater(first)) {
          // Distance to water edge
          let minDist = Infinity;
          for (let j = 0; j < waterPoly.length; j++) {
            const p1 = waterPoly[j];
            const p2 = waterPoly[(j + 1) % waterPoly.length];
            const dx = p2.x - p1.x, dy = p2.y - p1.y;
            const len2 = dx * dx + dy * dy || 1;
            const t = Math.max(0, Math.min(1, ((first.x - p1.x) * dx + (first.y - p1.y) * dy) / len2));
            const projX = p1.x + t * dx, projY = p1.y + t * dy;
            const dist = Math.hypot(projX - first.x, projY - first.y);
            minDist = Math.min(minDist, dist);
          }
          if (minDist < connectionSearchDist) {
            nearbyEndpoints.push({point: first, path: path, isFirst: true});
          }
        }
        
        // Check last endpoint
        const last = path[path.length - 1];
        if (!pointInAnyWater(last)) {
          let minDist = Infinity;
          for (let j = 0; j < waterPoly.length; j++) {
            const p1 = waterPoly[j];
            const p2 = waterPoly[(j + 1) % waterPoly.length];
            const dx = p2.x - p1.x, dy = p2.y - p1.y;
            const len2 = dx * dx + dy * dy || 1;
            const t = Math.max(0, Math.min(1, ((last.x - p1.x) * dx + (last.y - p1.y) * dy) / len2));
            const projX = p1.x + t * dx, projY = p1.y + t * dy;
            const dist = Math.hypot(projX - last.x, projY - last.y);
            minDist = Math.min(minDist, dist);
          }
          if (minDist < connectionSearchDist) {
            nearbyEndpoints.push({point: last, path: path, isFirst: false});
          }
        }
      }
      
      // Debug (suppressed): nearby endpoints count
      
      // Try to connect pairs of endpoints across water
      for (let i = 0; i < nearbyEndpoints.length; i++) {
        for (let j = i + 1; j < nearbyEndpoints.length; j++) {
          const ep1 = nearbyEndpoints[i];
          const ep2 = nearbyEndpoints[j];
          
          // Skip if same path
          if (ep1.path === ep2.path) continue;
          
          const dist = Math.hypot(ep2.point.x - ep1.point.x, ep2.point.y - ep1.point.y);
          if (dist > maxConnectionDist) continue;
          
          // Check if a straight line between them crosses this water body
          const crossings = findCrossings(ep1.point, ep2.point, waterPoly);
          // Debug (suppressed): testing endpoint pair for bridge
          
          // If no crossings, endpoints might BE at water edge already - check if line passes through water
          if (crossings.length === 0) {
            // Sample midpoint to see if bridge would cross water
            const mid = {x: (ep1.point.x + ep2.point.x) / 2, y: (ep1.point.y + ep2.point.y) / 2};
            if (pointInWater(mid, waterPoly)) {
              // Bridge would cross water - manually create bridge at street endpoints
              const bridgeStart = ep1.point;
              const bridgeEnd = ep2.point;
              const bridgeLen = dist;
              
              if (bridgeLen <= maxConnectionDist && !tooCloseToOthers(bridgeStart, bridgeEnd)) {
                // Helper to check if point is inside a polygon (ray casting)
                const pointInPolygon = (pt, poly) => {
                  let inside = false;
                  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
                    const xi = poly[i].x, yi = poly[i].y;
                    const xj = poly[j].x, yj = poly[j].y;
                    const intersect = ((yi > pt.y) !== (yj > pt.y)) && (pt.x < (xj - xi) * (pt.y - yi) / (yj - yi) + xi);
                    if (intersect) inside = !inside;
                  }
                  return inside;
                };
                
                // Check if bridge would hit any buildings
                let bridgeHitsBuilding = false;
                if (this.patches) {
                  const numSamples = 20;
                  for (let sample = 0; sample <= numSamples && !bridgeHitsBuilding; sample++) {
                    const t = sample / numSamples;
                    const testPoint = {
                      x: bridgeStart.x + (bridgeEnd.x - bridgeStart.x) * t,
                      y: bridgeStart.y + (bridgeEnd.y - bridgeStart.y) * t
                    };
                    
                    for (const patch of this.patches) {
                      if (!patch.ward || !patch.ward.geometry) continue;
                      for (const building of patch.ward.geometry) {
                        if (!building || building.length < 3) continue;
                        if (pointInPolygon(testPoint, building)) {
                          bridgeHitsBuilding = true;
                          break;
                        }
                      }
                      if (bridgeHitsBuilding) break;
                    }
                  }
                }
                
                if (!bridgeHitsBuilding) {
                  // Debug (suppressed): creating bridge with midpoint in water
                  this.bridges.push([bridgeStart, bridgeEnd]);
                  totalCrossings++;
                  
                  // Extend streets to bridge endpoints
                  if (ep1.isFirst) {
                    ep1.path.unshift(bridgeStart);
                    ep1.path.unshift(bridgeEnd);
                  } else {
                    ep1.path.push(bridgeStart);
                    ep1.path.push(bridgeEnd);
                  }
                  
                  if (ep2.isFirst) {
                    ep2.path.unshift(bridgeEnd);
                    ep2.path.unshift(bridgeStart);
                  } else {
                    ep2.path.push(bridgeEnd);
                    ep2.path.push(bridgeStart);
                  }
                  
                  // Debug (suppressed): extended paths for no-crossings case
                }
              }
            }
            continue;
          }
          
          if (crossings.length >= 2) {
            // Use the water crossing points as bridge ends (where streets meet water)
            // crossings[0] is entry point (closest to ep1), crossings[1] is exit point (closest to ep2)
            const bridgeStart = crossings[0];
            const bridgeEnd = crossings[1];
            const bridgeLen = Math.hypot(bridgeEnd.x - bridgeStart.x, bridgeEnd.y - bridgeStart.y);
            
            if (bridgeLen <= maxConnectionDist && !tooCloseToOthers(bridgeStart, bridgeEnd)) {
              // Verify endpoints aren't in other water bodies
              const ep1InOther = this.waterBodies.some(w => w !== waterPoly && pointInWater(ep1.point, w));
              const ep2InOther = this.waterBodies.some(w => w !== waterPoly && pointInWater(ep2.point, w));
              
              if (!ep1InOther && !ep2InOther) {
                // Helper to check if point is inside a polygon (ray casting)
                const pointInPolygon = (pt, poly) => {
                  let inside = false;
                  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
                    const xi = poly[i].x, yi = poly[i].y;
                    const xj = poly[j].x, yj = poly[j].y;
                    const intersect = ((yi > pt.y) !== (yj > pt.y)) && (pt.x < (xj - xi) * (pt.y - yi) / (yj - yi) + xi);
                    if (intersect) inside = !inside;
                  }
                  return inside;
                };
                
                // Check if bridge would hit any buildings by sampling many points along the bridge
                let bridgeHitsBuilding = false;
                if (this.patches) {
                  // Sample 20 points along the bridge line to catch any building intersections
                  const numSamples = 20;
                  for (let sample = 0; sample <= numSamples && !bridgeHitsBuilding; sample++) {
                    const t = sample / numSamples;
                    const testPoint = {
                      x: bridgeStart.x + (bridgeEnd.x - bridgeStart.x) * t,
                      y: bridgeStart.y + (bridgeEnd.y - bridgeStart.y) * t
                    };
                    
                    // Check if this point is inside any building
                    for (const patch of this.patches) {
                      if (!patch.ward || !patch.ward.geometry) continue;
                      for (const building of patch.ward.geometry) {
                        if (!building || building.length < 3) continue;
                        if (pointInPolygon(testPoint, building)) {
                          bridgeHitsBuilding = true;
                          break;
                        }
                      }
                      if (bridgeHitsBuilding) break;
                    }
                  }
                }
                
                if (!bridgeHitsBuilding) {
                  // Add the bridge
                  this.bridges.push([bridgeStart, bridgeEnd]);
                  totalCrossings++;
                  
                  // Extend streets to water edge and through bridge
                  // Add bridgeStart to ep1's path
                  if (ep1.isFirst) {
                    ep1.path.unshift(bridgeStart);
                    ep1.path.unshift(bridgeEnd);
                  } else {
                    ep1.path.push(bridgeStart);
                    ep1.path.push(bridgeEnd);
                  }
                  
                  // Add bridgeEnd to ep2's path  
                  if (ep2.isFirst) {
                    ep2.path.unshift(bridgeEnd);
                    ep2.path.unshift(bridgeStart);
                  } else {
                    ep2.path.push(bridgeEnd);
                    ep2.path.push(bridgeStart);
                  }
                  
                  // Debug (suppressed): extended paths lengths
                }
              }
            }
          }
        }
      }
    }
    // Summary: number of bridges created
    console.log('Bridges built:', totalCrossings);
  }
  
  // Ensure at least one bridge crosses major rivers that split the city
  ensureRiverCrossing() {
    if (!this.waterBodies || this.waterBodies.length === 0) return;
    if (!this.waterBodyTypes || this.waterBodyTypes.length === 0) return;
    if (!this.borderShape || this.borderShape.length < 3) return;
    
    // Helper: check if point is inside city walls
    const isInsideCity = (p) => {
      let inside = false;
      const poly = this.borderShape;
      for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
        const xi = poly[i].x, yi = poly[i].y;
        const xj = poly[j].x, yj = poly[j].y;
        const intersect = ((yi > p.y) !== (yj > p.y)) && (p.x < (xj - xi) * (p.y - yi) / (yj - yi) + xi);
        if (intersect) inside = !inside;
      }
      return inside;
    };
    
    // Find rivers (not coasts) that are wide enough to matter
    let forced = 0;
    for (let wi = 0; wi < this.waterBodies.length; wi++) {
      const water = this.waterBodies[wi];
      const type = this.waterBodyTypes[wi];
      // Debug (suppressed): water body inspection
      if (type !== 'river' && type !== 'canal') continue;
      if (!water || water.length < 4) continue;
      
      // Check if we already have bridges crossing this water body INSIDE the city
      let hasBridge = false;
      for (const bridge of this.bridges) {
        const [a, b] = bridge;
        const midpoint = new Point((a.x + b.x) / 2, (a.y + b.y) / 2);
        if (!isInsideCity(midpoint)) continue; // Only count bridges inside city
        
        // Check if bridge intersects this water body
        for (let j = 0; j < water.length; j++) {
          const c = water[j], d = water[(j + 1) % water.length];
          const r = {x: b.x - a.x, y: b.y - a.y};
          const s = {x: d.x - c.x, y: d.y - c.y};
          const denom = r.x * s.y - r.y * s.x;
          if (Math.abs(denom) < 1e-8) continue;
          const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
          const u = ((c.x - a.x) * r.y - (c.y - a.y) * r.x) / denom;
          if (t >= 0 && t <= 1 && u >= 0 && u <= 1) {
            hasBridge = true;
            break;
          }
        }
        if (hasBridge) break;
      }
      
      if (!hasBridge) {
        // No bridge present: generate a forced crossing
        
        if (type === 'canal') {
          // For CANAL: just place a perpendicular bridge through the city center
          // Debug (suppressed): generating perpendicular canal bridge
          
          // Find canal segments that pass through city bounds
          const cityMinY = Math.min(...this.borderShape.map(p => p.y));
          const cityMaxY = Math.max(...this.borderShape.map(p => p.y));
          const cityMinX = Math.min(...this.borderShape.map(p => p.x));
          const cityMaxX = Math.max(...this.borderShape.map(p => p.x));
          const cityCenterX = (cityMinX + cityMaxX) / 2;
          const cityCenterY = (cityMinY + cityMaxY) / 2;
          
          console.log('  City bounds: X', cityMinX.toFixed(1), 'to', cityMaxX.toFixed(1), 'Y', cityMinY.toFixed(1), 'to', cityMaxY.toFixed(1));
          console.log('  Canal polygon points:', water.map(p => '(' + p.x.toFixed(1) + ',' + p.y.toFixed(1) + ')').join(', '));
          
          // Robust orientation-based scan across canal within city
          const waterMinX = Math.min(...water.map(p => p.x));
          const waterMaxX = Math.max(...water.map(p => p.x));
          const waterMinY = Math.min(...water.map(p => p.y));
          const waterMaxY = Math.max(...water.map(p => p.y));
          const waterW = waterMaxX - waterMinX;
          const waterH = waterMaxY - waterMinY;
          const isVerticalCanal = waterH >= waterW;

          let crossings = [];
          let placed = false;
          const cityH = cityMaxY - cityMinY;
          const cityW = cityMaxX - cityMinX;
          const yCandidates = [0, 0.15, -0.15, 0.3, -0.3, 0.45, -0.45].map(f => cityCenterY + f * cityH);
          const xCandidates = [0, 0.15, -0.15, 0.3, -0.3, 0.45, -0.45].map(f => cityCenterX + f * cityW);

          if (isVerticalCanal) {
            for (const y of yCandidates) {
              if (y <= cityMinY || y >= cityMaxY) continue;
              if (y <= waterMinY || y >= waterMaxY) continue;
              crossings = [];
              const a = new Point(cityMinX - 500, y);
              const b = new Point(cityMaxX + 500, y);
              for (let j = 0; j < water.length; j++) {
                const c = water[j], d = water[(j + 1) % water.length];
                const r = {x: b.x - a.x, y: b.y - a.y};
                const s = {x: d.x - c.x, y: d.y - c.y};
                const denom = r.x * s.y - r.y * s.x;
                if (Math.abs(denom) < 1e-8) continue;
                const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
                const u = ((c.x - a.x) * r.y - (c.y - a.y) * r.x) / denom;
                if (t >= 0 && t <= 1 && u >= 0 && u <= 1) {
                  crossings.push(new Point(a.x + r.x * t, a.y + r.y * t));
                }
              }
              if (crossings.length >= 2) {
                crossings.sort((p, q) => p.x - q.x);
                let bestPair = null; let bestSpan = Infinity;
                for (let k = 0; k + 1 < crossings.length; k++) {
                  const span = Math.abs(crossings[k + 1].x - crossings[k].x);
                  if (span < bestSpan) { bestSpan = span; bestPair = [crossings[k], crossings[k + 1]]; }
                }
                if (bestPair) {
                  const [bridgeStart, bridgeEnd] = bestPair;
                  let hitsBuilding = false;
                  for (const patch of this.patches) {
                    if (!patch.ward || !patch.ward.buildings) continue;
                    for (const building of patch.ward.buildings) {
                      if (!building.shape || building.shape.length < 3) continue;
                      for (let kk = 0; kk < building.shape.length; kk++) {
                        const b1 = building.shape[kk];
                        const b2 = building.shape[(kk + 1) % building.shape.length];
                        const r2 = {x: bridgeEnd.x - bridgeStart.x, y: bridgeEnd.y - bridgeStart.y};
                        const s2 = {x: b2.x - b1.x, y: b2.y - b1.y};
                        const denom2 = r2.x * s2.y - r2.y * s2.x;
                        if (Math.abs(denom2) < 1e-8) continue;
                        const t2 = ((b1.x - bridgeStart.x) * s2.y - (b1.y - bridgeStart.y) * s2.x) / denom2;
                        const u2 = ((b1.x - bridgeStart.x) * r2.y - (b1.y - bridgeStart.y) * r2.x) / denom2;
                        if (t2 >= 0 && t2 <= 1 && u2 >= 0 && u2 <= 1) { hitsBuilding = true; break; }
                      }
                      if (hitsBuilding) break;
                    }
                    if (hitsBuilding) break;
                  }
                  if (!hitsBuilding) {
                    this.bridges.push([bridgeStart, bridgeEnd]);
                    forced++;
                    placed = true;
                    break;
                  }
                }
              }
            }
          } else {
            for (const x of xCandidates) {
              if (x <= cityMinX || x >= cityMaxX) continue;
              if (x <= waterMinX || x >= waterMaxX) continue;
              crossings = [];
              const a = new Point(x, cityMinY - 500);
              const b = new Point(x, cityMaxY + 500);
              for (let j = 0; j < water.length; j++) {
                const c = water[j], d = water[(j + 1) % water.length];
                const r = {x: b.x - a.x, y: b.y - a.y};
                const s = {x: d.x - c.x, y: d.y - c.y};
                const denom = r.x * s.y - r.y * s.x;
                if (Math.abs(denom) < 1e-8) continue;
                const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
                const u = ((c.x - a.x) * r.y - (c.y - a.y) * r.x) / denom;
                if (t >= 0 && t <= 1 && u >= 0 && u <= 1) {
                  crossings.push(new Point(a.x + r.x * t, a.y + r.y * t));
                }
              }
              if (crossings.length >= 2) {
                crossings.sort((p, q) => p.y - q.y);
                let bestPair = null; let bestSpan = Infinity;
                for (let k = 0; k + 1 < crossings.length; k++) {
                  const span = Math.abs(crossings[k + 1].y - crossings[k].y);
                  if (span < bestSpan) { bestSpan = span; bestPair = [crossings[k], crossings[k + 1]]; }
                }
                if (bestPair) {
                  const [bridgeStart, bridgeEnd] = bestPair;
                  let hitsBuilding = false;
                  for (const patch of this.patches) {
                    if (!patch.ward || !patch.ward.buildings) continue;
                    for (const building of patch.ward.buildings) {
                      if (!building.shape || building.shape.length < 3) continue;
                      for (let kk = 0; kk < building.shape.length; kk++) {
                        const b1 = building.shape[kk];
                        const b2 = building.shape[(kk + 1) % building.shape.length];
                        const r2 = {x: bridgeEnd.x - bridgeStart.x, y: bridgeEnd.y - bridgeStart.y};
                        const s2 = {x: b2.x - b1.x, y: b2.y - b1.y};
                        const denom2 = r2.x * s2.y - r2.y * s2.x;
                        if (Math.abs(denom2) < 1e-8) continue;
                        const t2 = ((b1.x - bridgeStart.x) * s2.y - (b1.y - bridgeStart.y) * s2.x) / denom2;
                        const u2 = ((b1.x - bridgeStart.x) * r2.y - (b1.y - bridgeStart.y) * r2.x) / denom2;
                        if (t2 >= 0 && t2 <= 1 && u2 >= 0 && u2 <= 1) { hitsBuilding = true; break; }
                      }
                      if (hitsBuilding) break;
                    }
                    if (hitsBuilding) break;
                  }
                  if (!hitsBuilding) {
                    this.bridges.push([bridgeStart, bridgeEnd]);
                    forced++;
                    placed = true;
                    break;
                  }
                }
              }
            }
          }
          // Debug (suppressed): failed to place canal bridge after scanning slices
          
          if (crossings.length >= 2) {
            // Check if bridge line hits any buildings
            const bridgeStart = crossings[0];
            const bridgeEnd = crossings[crossings.length - 1];
            let hitsBuilding = false;
            
            for (const patch of this.patches) {
              if (!patch.ward || !patch.ward.buildings) continue;
              for (const building of patch.ward.buildings) {
                if (!building.shape || building.shape.length < 3) continue;
                // Check if bridge line intersects building polygon
                for (let k = 0; k < building.shape.length; k++) {
                  const b1 = building.shape[k];
                  const b2 = building.shape[(k + 1) % building.shape.length];
                  const r = {x: bridgeEnd.x - bridgeStart.x, y: bridgeEnd.y - bridgeStart.y};
                  const s = {x: b2.x - b1.x, y: b2.y - b1.y};
                  const denom = r.x * s.y - r.y * s.x;
                  if (Math.abs(denom) < 1e-8) continue;
                  const t = ((b1.x - bridgeStart.x) * s.y - (b1.y - bridgeStart.y) * s.x) / denom;
                  const u = ((b1.x - bridgeStart.x) * r.y - (b1.y - bridgeStart.y) * r.x) / denom;
                  if (t >= 0 && t <= 1 && u >= 0 && u <= 1) {
                    hitsBuilding = true;
                    break;
                  }
                }
                if (hitsBuilding) break;
              }
              if (hitsBuilding) break;
            }
            
            if (!hitsBuilding) {
              this.bridges.push([bridgeStart, bridgeEnd]);
              forced++;
            } else {
              // Debug (suppressed): bridge skipped due to building hit
            }
          }
        }
      }
    }
    if (forced > 0) {
      console.log('Forced bridges:', forced);
    }
  }
  
  // Generate random piers along water edges for visual interest
  generatePiers() {
    if (!this.waterBodies || this.waterBodies.length === 0) return;
    if (!this.piers) this.piers = [];
    
    const streetW = (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0;
    const pierLength = streetW * 2.5;
    const pierWidth = streetW * 0.8;
    
    // Helper: check if a point is inside any OTHER water body (for overlap detection)
    const isInOtherWater = (point, currentWater) => {
      for (const otherWater of this.waterBodies) {
        if (otherWater === currentWater) continue;
        if (!otherWater || otherWater.length < 3) continue;
        
        // Point-in-polygon test
        let inside = false;
        for (let i = 0, j = otherWater.length - 1; i < otherWater.length; j = i++) {
          const xi = otherWater[i].x, yi = otherWater[i].y;
          const xj = otherWater[j].x, yj = otherWater[j].y;
          const intersect = ((yi > point.y) !== (yj > point.y)) && 
                           (point.x < (xj - xi) * (point.y - yi) / (yj - yi) + xi);
          if (intersect) inside = !inside;
        }
        if (inside) return true;
      }
      return false;
    };
    
    // Generate 2-5 piers per water body
    for (const water of this.waterBodies) {
      if (!water || water.length < 4) continue;
      
      const numPiers = 2 + Random.int(0, 4);
      const usedIndices = new Set();
      let piersAdded = 0;
      
      for (let p = 0; p < numPiers && piersAdded < numPiers; p++) {
        // Pick random point on water edge
        let idx = Random.int(0, water.length);
        let attempts = 0;
        while (usedIndices.has(idx) && attempts < 20) {
          idx = Random.int(0, water.length);
          attempts++;
        }
        if (attempts >= 20) continue;
        
        usedIndices.add(idx);
        const edgeStart = water[idx];
        const edgeEnd = water[(idx + 1) % water.length];
        
        // Skip if this edge point overlaps with another water body
        if (isInOtherWater(edgeStart, water) || isInOtherWater(edgeEnd, water)) {
          continue;
        }
        
        // Pier juts out perpendicular to water edge
        const ex = edgeEnd.x - edgeStart.x;
        const ey = edgeEnd.y - edgeStart.y;
        const len = Math.hypot(ex, ey) || 1e-6;
        const ux = ex / len, uy = ey / len;
        const nx = -uy, ny = ux; // perpendicular (inward)
        
        // Place pier somewhere along edge
        const t = 0.2 + Random.float() * 0.6;
        const baseX = edgeStart.x + ex * t;
        const baseY = edgeStart.y + ey * t;
        
        // Check if pier base overlaps with another water body
        const pierBase = new Point(baseX, baseY);
        if (isInOtherWater(pierBase, water)) {
          continue;
        }
        
        // Pier extends inward (into land)
        const pierEnd = new Point(baseX + nx * pierLength, baseY + ny * pierLength);
        
        // Check if pier end overlaps with another water body
        if (isInOtherWater(pierEnd, water)) {
          continue;
        }
        
        this.piers.push({
          start: new Point(baseX, baseY),
          end: pierEnd,
          width: pierWidth
        });
        piersAdded++;
      }
    }
    
    console.log('Piers built:', this.piers.length);
  }
  
  // Tag DCEL edges that run along streets/exterior roads
  markRoadEdgesFromStreets() {
    if (!this.faces || !this.streets) return;
    const streetWidth = (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0;
    const half = streetWidth * 0.5;

    const allPaths = [];
    if (Array.isArray(this.streets)) allPaths.push(...this.streets);
    if (Array.isArray(this.exteriorRoads)) allPaths.push(...this.exteriorRoads);

    const distPointSeg = (p, a, b) => {
      const abx = b.x - a.x, aby = b.y - a.y;
      const apx = p.x - a.x, apy = p.y - a.y;
      const ab2 = abx * abx + aby * aby || 1e-6;
      let t = (apx * abx + apy * aby) / ab2; t = Math.max(0, Math.min(1, t));
      const x = a.x + abx * t, y = a.y + aby * t;
      const dx = p.x - x, dy = p.y - y;
      return Math.sqrt(dx * dx + dy * dy);
    };

    const segDist = (a, b, c, d) => {
      // Approximate as min distance from endpoints to opposite segments
      return Math.min(
        distPointSeg(a, c, d),
        distPointSeg(b, c, d),
        distPointSeg(c, a, b),
        distPointSeg(d, a, b)
      );
    };

    for (const face of this.faces) {
      if (!face.patch || !face.patch.withinCity) continue;
      for (const e of face.edges()) {
        if (e.data === EdgeType.WALL || e.data === EdgeType.WATER) continue; // keep boundary/water classification
        const [ea, eb] = e.asSegment();
        let near = false;
        for (const path of allPaths) {
          for (let i = 0; i < path.length - 1; i++) {
            const a = path[i], b = path[i + 1];
            const d = segDist(ea, eb, a, b);
            if (d <= half * 0.9) { near = true; break; }
          }
          if (near) break;
        }
        if (near) e.data = EdgeType.ROAD;
      }
    }
  }
  
  buildTopology() {
    const graph = new Map();
    const bridgePenalty = 3.0; // make bridges more expensive than normal streets
    
    for (const patch of this.patches) {
      if (patch.waterbody) continue;
      if (!patch.shape || patch.shape.length < 3) continue;
      
      for (let i = 0; i < patch.shape.length; i++) {
        const v0 = patch.shape[i];
        const v1 = patch.shape[(i + 1) % patch.shape.length];
        
        // Skip null or invalid vertices
        if (!v0 || !v1 || v0.x === undefined || v0.y === undefined || v1.x === undefined || v1.y === undefined) {
          console.warn('Skipping invalid vertex in patch shape');
          continue;
        }
        
        // Determine water crossing
        let crossesWater = false;
        if (this.waterBodies && this.waterBodies.length > 0) {
          for (const poly of this.waterBodies) {
            if (segmentIntersectsPolygon(v0, v1, poly)) { crossesWater = true; break; }
          }
        }
        
        if (!graph.has(v0)) graph.set(v0, {edges: new Map()});
        if (!graph.has(v1)) graph.set(v1, {edges: new Map()});
        
        const isWallEdge = this.borderShape && (
          (this.borderShape.includes(v0) && this.borderShape.includes(v1))
        );
        
        const isGateEdge = this.gates.some(g => 
          (g.x === v0.x && g.y === v0.y) || (g.x === v1.x && g.y === v1.y)
        );
        
        if (isWallEdge && !isGateEdge) continue;
        
        let dist = Point.distance(v0, v1, 'buildTopology/edgeLen');
        if (crossesWater) {
          dist *= bridgePenalty; // allow crossing but make it costly
        }
        graph.get(v0).edges.set(v1, dist);
        graph.get(v1).edges.set(v0, dist);
      }
    }
    
    console.log('Topology nodes:', graph.size);
    return graph;
  }
  
  findPath(graph, start, end) {
    // Validate inputs early
    if (!graph || graph.size === 0) return null;
    if (!start || start.x === undefined || start.y === undefined) return null;
    if (!end || end.x === undefined || end.y === undefined) return null;
    // Find closest graph vertices to start and end
    let closestStart = null;
    let closestEnd = null;
    let minStartDist = Infinity;
    let minEndDist = Infinity;
    
    for (const vertex of graph.keys()) {
      if (!vertex || vertex.x === undefined || vertex.y === undefined) continue;
      const startDist = Point.distance(vertex, start, 'findPath/closestStart');
      if (startDist < minStartDist) {
        minStartDist = startDist;
        closestStart = vertex;
      }
      
      const endDist = Point.distance(vertex, end, 'findPath/closestEnd');
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
    fScore.set(closestStart, Point.distance(closestStart, closestEnd, 'findPath/initF'));
    
    let iterations = 0;
    // Reasonable safety limit - cap at 10,000 iterations regardless of graph size
    const maxIterations = Math.min(10000, Math.max(3000, graph.size * 20));
    
    // Track best node found (closest to end) for partial path fallback
    let bestNode = closestStart;
    let bestDist = Point.distance(closestStart, closestEnd, 'findPath/bestInit');
    
    while (openSet.size > 0 && iterations < maxIterations) {
      iterations++;
      
      // Find node in openSet with lowest fScore
      let current = null;
      let lowestF = Infinity;
      for (const node of openSet) {
        const f = fScore.has(node) ? fScore.get(node) : Infinity;
        if (current === null || f <= lowestF) {
          lowestF = f;
          current = node;
        }
      }
      if (current === null) {
        // No valid node picked; break and return best partial
        break;
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
      
      // Track best progress towards goal
      const distToEnd = Point.distance(current, closestEnd, 'findPath/progress');
      if (distToEnd < bestDist) {
        bestDist = distToEnd;
        bestNode = current;
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
          fScore.set(neighbor, tentativeG + Point.distance(neighbor, closestEnd, 'findPath/heuristic'));
          openSet.add(neighbor);
        }
      }
    }
    
    if (iterations >= maxIterations) {
      console.warn('A* pathfinding exceeded max iterations - returning partial path');
      // Return partial path to best node found
      if (bestNode && cameFrom.has(bestNode)) {
        const path = [bestNode];
        let current = bestNode;
        while (cameFrom.has(current)) {
          current = cameFrom.get(current);
          path.unshift(current);
        }
        path.unshift(start);
        return path;
      }
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
    // Filter out waterbody patches when creating wards
    const innerPatches = this.patches.filter(p => 
      p.withinCity && p !== this.plaza && p !== this.citadel && !p.waterbody
    );
    
    // Plaza if needed
    if (this.plaza) {
      this.plaza.ward = new Plaza(this, this.plaza);
    }

    // Citadel outside walls if enabled
    if (this.citadel && this.citadelNeeded) {
      this.citadel.ward = new Castle(this, this.citadel);
    }
    // Urban castle inside walls if enabled (independent of citadel)
    if (StateManager.urbanCastle) {
      const candidates = innerPatches.filter(p => p !== this.plaza && p !== this.citadel && !p.waterbody);
      const central = candidates.sort((a,b)=>{
        const ca=Polygon.centroid(a.shape), cb=Polygon.centroid(b.shape);
        return Point.distance(ca,new Point(0,0)) - Point.distance(cb,new Point(0,0));
      })[0];
      if (central) central.ward = new Castle(this, central);
    }
    
    for (const patch of innerPatches) {
      // Skip patches that already have a ward assigned (plaza, urban castle, etc.)
      if (patch.ward) continue;
      
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
    // Less likely near city (where slums would form), more likely farther away
    for (const patch of this.patches) {
      if (!patch.withinCity && !patch.ward && !patch.waterbody) {
        const compactness = this.calculateCompactness(patch.shape);
        
        // Calculate distance from city center
        const patchCenter = Polygon.centroid(patch.shape);
        const distFromCenter = Math.sqrt(patchCenter.x * patchCenter.x + patchCenter.y * patchCenter.y);
        const distFromCityEdge = Math.max(0, distFromCenter - this.cityRadius);
        
        // Farms less likely near city (where slums form), more likely far away
        // Near city: 0% chance, Far from city: 45% chance
        const baseFarmChance = 0 + Math.min(0.25, distFromCityEdge / (this.cityRadius * 2));
        
        if (Random.chance(baseFarmChance) && compactness >= 0.6) {
          patch.ward = new Farm(this, patch);
        }
      }
    }

    // Optional shantytown - organic clusters along roads with density falloff
    if (StateManager.shantytown) {
      this.generateShantytown();
    }
  }
  
  generateShantytown() {
    // Generate organic network like brick/stone pattern around streets/gates
    // Radial spokes from gates with short arc segments connecting them (brick-like)
    // NO alleys far from streets - only where connected to roads/gates
    
    const outsidePatches = this.patches.filter(p => 
      !p.withinCity && !p.ward && !p.waterbody && p.shape && p.shape.length >= 3
    );
    
    if (outsidePatches.length === 0) return;
    
    // Use gates if available, otherwise use border points
    const startPoints = (this.gates && this.gates.length > 0) ? this.gates : 
                        (this.borderShape && this.borderShape.length > 0) ? 
                        [this.borderShape[0], this.borderShape[Math.floor(this.borderShape.length / 3)], 
                         this.borderShape[Math.floor(2 * this.borderShape.length / 3)]] : [];
    
    if (startPoints.length === 0) return;
    
    const shantyPaths = [];
    const radialSpokes = []; // Store radial spokes for creating brick pattern
    const alleyWidth = StateManager.alleyWidth || 1.8;
    const maxRadius = this.cityRadius * 100;
    const cityCenter = Polygon.centroid(this.borderShape || []);
    
    // Collect exterior roads that aren't alleys
    const existingRoads = (this.exteriorRoads || []).filter(r => !r.isAlley);
    
    // Generate network nodes
    const nodes = [];
    
    // STEP 1: Define arc rings - 40 rings extending to maxRadius
    const arcRings = [];
    const numRings = 40;
    const totalSpan = maxRadius - this.cityRadius * 5;
    const ringSpacing = totalSpan / numRings;
    
    for (let ring = 0; ring < numRings; ring++) {
      const arcRadius = this.cityRadius + ring * ringSpacing  * 0.1;
      arcRings.push({ radius: arcRadius, segments: [] });
    }
    
    // STEP 2: Create radials that ONLY exist near streets and travel FAR down the roads
    const allRadials = [];
    
    for (const road of existingRoads) {
      if (road.length < 3) continue;
      
      const midIdx = Math.floor(road.length / 2);
      const roadAngle = Math.atan2(road[midIdx].y - cityCenter.y, road[midIdx].x - cityCenter.x);
      const roadPos = road[midIdx];
      
      // 8-15 radials PER STREET, evenly spaced
      const numRadials = 6 + Random.int(0, 8);
      
      // Calculate even spacing - same as ring spacing
      const ringSpacing = arcRings.length > 1 ? arcRings[1].radius - arcRings[0].radius : maxRadius * 0.03;
      const avgRadius = (this.cityRadius + maxRadius) / 2;
      const radialAngularSpacing = ringSpacing / avgRadius;
      
      for (let r = 0; r < numRadials; r++) {
        // EVENLY SPACED radials
        const angleOffset = (r - (numRadials - 1) / 2) * radialAngularSpacing;
        let currentAngle = roadAngle + angleOffset;
        
        const radialSegments = [];
        let currentSegment = [];
        let currentRadius = this.cityRadius * .8;
        
        // ALL radials from this street go FAR - to 95% of maxRadius
        const radialMaxRadius = maxRadius * 10;
        
        while (currentRadius < radialMaxRadius) {
          const normalizedDist = (currentRadius - this.cityRadius) / (maxRadius - this.cityRadius);
          
          // Current position
          const x = cityCenter.x + Math.cos(currentAngle) * currentRadius;
          const y = cityCenter.y + Math.sin(currentAngle) * currentRadius;
          const currentPos = new Point(x, y);
          
          // Distance from this street for arc fade
          const distFromStreet = Point.distance(currentPos, roadPos);
          const normalizedStreetDist = distFromStreet / maxRadius;
          
          // Arcs fade RADIALLY from streets - much faster falloff
          const arcFadeProb = Math.pow(1 - normalizedStreetDist, 2.5);
          
          // Check if we're crossing an arc ring
          let nearRing = null;
          let ringIndex = -1;
          for (let i = 0; i < arcRings.length; i++) {
            if (Math.abs(currentRadius - arcRings[i].radius) < alleyWidth * 3.5) {
              nearRing = arcRings[i];
              ringIndex = i;
              break;
            }
          }
          
          // ALWAYS make left/right decision at intersections
          // Skip the first ring (index 0) to avoid ghostly circle around city
          if (nearRing && ringIndex > 0) {
            // Check if arc is still active at this distance from street
            if (Random.float() < arcFadeProb) {
              // WRAP AROUND THE ARC
              // Save current radial segment
              if (currentSegment.length >= 2) {
                radialSegments.push([...currentSegment]);
              }
              currentSegment = [];
              
              // Choose direction (left or right around circle)
              const wrapDirection = Random.float() < 0.5 ? 1 : -1;
              const wrapAngle = (0.15 + Random.float() * 0.25) * Math.PI; // 15-40 degrees
              const startAngle = currentAngle;
              const endAngle = currentAngle + wrapDirection * wrapAngle;
              
              // Travel along arc
              const arcSegment = [];
              const numArcSteps = 6 + Random.int(0, 8);
              for (let a = 0; a <= numArcSteps; a++) {
                const t = a / numArcSteps;
                const angle = startAngle + (endAngle - startAngle) * t;
                
                const arcX = cityCenter.x + Math.cos(angle) * nearRing.radius;
                const arcY = cityCenter.y + Math.sin(angle) * nearRing.radius;
                
                const variation = alleyWidth * 0.3;
                const pt = new Point(
                  arcX + (Random.float() - 0.5) * variation,
                  arcY + (Random.float() - 0.5) * variation
                );
                
                arcSegment.push(pt);
              }
              
              if (arcSegment.length >= 2) {
                nearRing.segments.push(arcSegment);
                radialSegments.push(arcSegment);
              }
              
              // 25% chance to terminate after wrapping
              if (Random.float() < 0.25) {
                break;
              }
              
              // Update angle and continue outward
              currentAngle = endAngle;
              currentRadius = nearRing.radius + alleyWidth * (3 + Random.float() * 3);
            } else {
              // Arc faded out - just skip past it
              currentRadius += alleyWidth * (3 + Random.float() * 2);
            }
          } else {
            // Continue straight outward
            const variation = alleyWidth * 0.3;
            const pt = new Point(
              x + (Random.float() - 0.5) * variation,
              y + (Random.float() - 0.5) * variation
            );
            
            currentSegment.push(pt);
            currentRadius += alleyWidth * (4 + Random.float() * 3);
          }
        }
        
        // Save final segment
        if (currentSegment.length >= 2) {
          radialSegments.push(currentSegment);
        }
        
        // Add all segments from this radial
        shantyPaths.push(...radialSegments);
      }
    }

    
    // Place shanties along the alleyway network
    for (const patch of outsidePatches) {
      const c = Polygon.centroid(patch.shape);
      
      // Find nearest distance to any alley path
      let minPathDist = Infinity;
      let nearestPathPoint = null;
      
      for (const path of shantyPaths) {
        for (let i = 0; i < path.length - 1; i++) {
          const dist = this.pointToSegmentDistance(c, path[i], path[i + 1]);
          if (dist < minPathDist) {
            minPathDist = dist;
            // Find closest point on this segment
            const segLen = Point.distance(path[i], path[i + 1]);
            const t = Math.max(0, Math.min(1, 
              ((c.x - path[i].x) * (path[i + 1].x - path[i].x) + 
               (c.y - path[i].y) * (path[i + 1].y - path[i].y)) / (segLen * segLen)
            ));
            nearestPathPoint = new Point(
              path[i].x + t * (path[i + 1].x - path[i].x),
              path[i].y + t * (path[i + 1].y - path[i].y)
            );
          }
        }
      }
      
      // Find distance from city center for fade
      const distFromCity = Point.distance(c, cityCenter);
      const normalizedCityDist = (distFromCity - this.cityRadius) / (maxRadius - this.cityRadius);
      
      // Place shanty based on hierarchy: streets > alleys near streets > alleys far from streets
      // Find nearest street (non-alley road)
      let minStreetDist = Infinity;
      for (const road of existingRoads) {
        for (let i = 0; i < road.length - 1; i++) {
          const dist = this.pointToSegmentDistance(c, road[i], road[i + 1]);
          if (dist < minStreetDist) minStreetDist = dist;
        }
      }
      
      const streetThreshold = alleyWidth * 12;
      const alleyThreshold = alleyWidth * 6;
      
      // INVERSE SQUARE ROOT BOOST: Buildings near city+streets get massive density increase
      // distFromCity is in world units from city edge
      // ONLY APPLY OUTSIDE THE CITY (distFromCity > cityRadius)
      const isOutsideCity = distFromCity > this.cityRadius;
      const cityDistBoost = isOutsideCity ? 1.0 / Math.sqrt(Math.max(1, distFromCity - this.cityRadius)) : 1.0;
      
      let probability = 0;
      
      // Priority 1: Near streets (very high priority)
      if (minStreetDist < streetThreshold) {
        const streetProximity = 1 - (minStreetDist / streetThreshold);
        const cityFade = Math.pow(1 - Math.min(1, normalizedCityDist), 0.5);
        probability = Math.pow(streetProximity, 0.4) * cityFade * 0.7 * cityDistBoost;
      }
      // Priority 2: Near alleys that are close to streets (medium priority)
      else if (minPathDist < alleyThreshold && nearestPathPoint) {
        const alleyProximity = 1 - (minPathDist / alleyThreshold);
        
        // How close is this alley to streets?
        let alleyToStreetDist = Infinity;
        for (const road of existingRoads) {
          for (let i = 0; i < road.length - 1; i++) {
            const dist = this.pointToSegmentDistance(nearestPathPoint, road[i], road[i + 1]);
            if (dist < alleyToStreetDist) alleyToStreetDist = dist;
          }
        }
        
        const alleyStreetProximity = 1 - Math.min(1, alleyToStreetDist / (maxRadius * 0.3));
        const cityFade = Math.pow(1 - Math.min(1, normalizedCityDist), 0.7);
        probability = Math.pow(alleyProximity, 0.5) * alleyStreetProximity * cityFade * 0.45 * cityDistBoost;
      }
      // Priority 3: Near alleys far from streets (low priority)
      else if (minPathDist < alleyThreshold) {
        const alleyProximity = 1 - (minPathDist / alleyThreshold);
        const cityFade = Math.pow(1 - Math.min(1, normalizedCityDist), 0.9);
        probability = Math.pow(alleyProximity, 0.7) * cityFade * 0.25 * cityDistBoost;
      }
      
      // 300% BASE INCREASE for slum wards + 200% overall density boost
      if (Random.float() < probability * 30.0) {
        patch.ward = new Slum(this, patch);
      }
    }
    
    // Store paths for rendering
    if (!this.exteriorRoads) this.exteriorRoads = [];
    for (const path of shantyPaths) {
      path.isAlley = true;
      this.exteriorRoads.push(path);
    }
  }
  
  getOutwardDirection(gate) {
    // Find direction perpendicular to wall at gate
    if (!this.borderShape || this.borderShape.length < 3) return { x: 1, y: 0 };
    
    // Find closest wall segment to gate
    let closestDist = Infinity;
    let closestSegment = null;
    
    for (let i = 0; i < this.borderShape.length; i++) {
      const a = this.borderShape[i];
      const b = this.borderShape[(i + 1) % this.borderShape.length];
      const dist = this.pointToSegmentDistance(gate, a, b);
      if (dist < closestDist) {
        closestDist = dist;
        closestSegment = { a, b };
      }
    }
    
    if (!closestSegment) return { x: 1, y: 0 };
    
    // Get perpendicular pointing outward
    const wallDir = {
      x: closestSegment.b.x - closestSegment.a.x,
      y: closestSegment.b.y - closestSegment.a.y
    };
    const len = Math.sqrt(wallDir.x * wallDir.x + wallDir.y * wallDir.y);
    wallDir.x /= len;
    wallDir.y /= len;
    
    // Perpendicular directions
    const perp1 = { x: -wallDir.y, y: wallDir.x };
    const perp2 = { x: wallDir.y, y: -wallDir.x };
    
    // Choose perpendicular that points away from city center
    const dot1 = perp1.x * gate.x + perp1.y * gate.y;
    const dot2 = perp2.x * gate.x + perp2.y * gate.y;
    
    return dot1 > dot2 ? perp1 : perp2;
  }
  
  pointToSegmentDistance(point, a, b) {
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const len2 = dx * dx + dy * dy;
    if (len2 === 0) return Point.distance(point, a);
    
    let t = ((point.x - a.x) * dx + (point.y - a.y) * dy) / len2;
    t = Math.max(0, Math.min(1, t));
    
    const projX = a.x + t * dx;
    const projY = a.y + t * dy;
    return Math.sqrt((point.x - projX) ** 2 + (point.y - projY) ** 2);
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

  // Generate named districts by clustering adjacent wards
  generateDistricts() {
    this.districts = [];
    if (!StateManager.showRegionNames) return;

    const innerPatches = this.patches.filter(p => p.withinCity && !p.waterbody && p.ward);
    if (innerPatches.length === 0) return;

    const used = new Set();
    const targetDistricts = Math.max(3, Math.floor(innerPatches.length / 4));

    // Start districts from random seed patches
    for (let i = 0; i < targetDistricts && used.size < innerPatches.length; i++) {
      const available = innerPatches.filter(p => !used.has(p));
      if (available.length === 0) break;

      const seed = available[Random.int(0, available.length)];
      const district = { patches: [seed], name: DistrictNameGenerator.generate() };
      used.add(seed);

      // Grow district by adding adjacent patches
      const maxSize = Math.floor(innerPatches.length / targetDistricts) + Random.int(0, 3);
      for (let j = 0; j < maxSize - 1; j++) {
        const candidates = [];
        for (const p of district.patches) {
          for (const neighbor of this.patches) {
            if (!used.has(neighbor) && neighbor.withinCity && !neighbor.waterbody && neighbor.ward) {
              if (this.areAdjacent(p, neighbor)) {
                candidates.push(neighbor);
              }
            }
          }
        }
        if (candidates.length === 0) break;
        const next = candidates[Random.int(0, candidates.length)];
        district.patches.push(next);
        used.add(next);
      }

      if (district.patches.length >= 2) {
        this.districts.push(district);
      }
    }
  }

  areAdjacent(p1, p2) {
    // Check if two patches share vertices
    for (const v1 of p1.shape) {
      for (const v2 of p2.shape) {
        if (Math.hypot(v1.x - v2.x, v1.y - v2.y) < 0.5) return true;
      }
    }
    return false;
  }

  // Generate symmetric building strips along exterior roads within outside patches.
  // Buildings are clipped to outside patches and respect water at render time.
  buildOutsideSettlements() {
    if (!Array.isArray(this.exteriorRoads) || this.exteriorRoads.length === 0) return;
    const outsidePatches = this.patches.filter(p => !p.withinCity && !p.waterbody);
    if (outsidePatches.length === 0) return;

    const streetWidth = (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0;
    const gap = (StateManager.buildingGap !== undefined) ? StateManager.buildingGap : 1.6;
    const depthBase = 5.5; // base building depth from road centerline
    const targetFacade = 5.5; // target facade width along road

    const pointInPoly = (pt, poly) => {
      let inside=false; for(let i=0,j=poly.length-1;i<poly.length;j=i++){
        const xi=poly[i].x, yi=poly[i].y, xj=poly[j].x, yj=poly[j].y;
        const inter=((yi>pt.y)!=(yj>pt.y)) && (pt.x < (xj-xi)*(pt.y-yi)/(yj-yi)+xi); if (inter) inside=!inside;
      } return inside;
    };
    const segmentClipToPoly = (a, b, poly) => {
      // Return array of [p0,p1] segments lying inside poly
      // Find all intersections and build intervals
      const ts = [];
      const r = {x: b.x - a.x, y: b.y - a.y};
      for (let i=0;i<poly.length;i++){
        const c = poly[i], d = poly[(i+1)%poly.length];
        const s = {x: d.x - c.x, y: d.y - c.y};
        const denom = r.x * s.y - r.y * s.x; if (Math.abs(denom) < 1e-8) continue;
        const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
        const u = ((c.x - a.x) * r.y - (c.y - a.y) * r.x) / denom;
        if (t >= 0 && t <= 1 && u >= 0 && u <= 1) ts.push(Math.max(0, Math.min(1, t)));
      }
      ts.sort((x,y)=>x-y);
      // Ensure endpoints considered
      const aIn = pointInPoly(a, poly);
      const bIn = pointInPoly(b, poly);
      const tvals = [];
      if (aIn) tvals.push(0);
      for (const t of ts) tvals.push(t);
      if (bIn) tvals.push(1);
      // Build pairs alternating inside/outside starting with aIn
      const segments = [];
      if (tvals.length === 0) return segments;
      let inside = aIn;
      let prevT = tvals[0];
      // Merge duplicates
      const uniq = [tvals[0]];
      for (let i=1;i<tvals.length;i++){ if (Math.abs(tvals[i]-uniq[uniq.length-1])>1e-6) uniq.push(tvals[i]); }
      for (const t of uniq){
        if (!inside) { inside = true; prevT = t; }
        else {
          const t0 = prevT, t1 = t;
          if (t1 - t0 > 1e-4) {
            const p0 = new Point(a.x + r.x * t0, a.y + r.y * t0);
            const p1 = new Point(a.x + r.x * t1, a.y + r.y * t1);
            segments.push([p0,p1]);
          }
          inside = false;
        }
      }
      return segments;
    };

    const makeStripBuildings = (p0, p1, depthScale=1.0) => {
      const dx = p1.x - p0.x, dy = p1.y - p0.y; const len = Math.hypot(dx,dy) || 1e-6;
      const nx = -dy/len, ny = dx/len;
      const out = streetWidth*0.5 + gap; // from centerline to near edge
      const inner = out + depthBase*depthScale;         // from centerline to inner edge of buildings
      // Quad on one side
      const a1 = new Point(p0.x + nx*out, p0.y + ny*out);
      const b1 = new Point(p1.x + nx*out, p1.y + ny*out);
      const c1 = new Point(p1.x + nx*inner, p1.y + ny*inner);
      const d1 = new Point(p0.x + nx*inner, p0.y + ny*inner);
      // Opposite side
      const a2 = new Point(p0.x - nx*out, p0.y - ny*out);
      const b2 = new Point(p1.x - nx*out, p1.y - ny*out);
      const c2 = new Point(p1.x - nx*inner, p1.y - ny*inner);
      const d2 = new Point(p0.x - nx*inner, p0.y - ny*inner);
      const strips = [ [a1,b1,c1,d1], [a2,b2,c2,d2] ];
      // Subdivide strips into row buildings
      const count = Math.max(1, Math.floor(len / targetFacade));
      const rows = [];
      for (const s of strips){
        const [sa,sb,sc,sd] = s;
        for (let k=0;k<count;k++){
          const t0=k/count, t1=(k+1)/count;
          const pA = new Point(sa.x + (sb.x-sa.x)*t0, sa.y + (sb.y-sa.y)*t0);
          const pB = new Point(sa.x + (sb.x-sa.x)*t1, sa.y + (sb.y-sa.y)*t1);
          const pC = new Point(sd.x + (sc.x-sd.x)*t1, sd.y + (sc.y-sd.y)*t1);
          const pD = new Point(sd.x + (sc.x-sd.x)*t0, sd.y + (sc.y-sd.y)*t0);
          rows.push([pA,pB,pC,pD]);
        }
      }
      return rows;
    };

    // Check if shantytown mode is enabled and has alleys
    const hasShantytownAlleys = this.exteriorRoads && this.exteriorRoads.some(r => r.isAlley);
    const alleyWidth = StateManager.alleyWidth || 1.8;
    
    // For each outside patch, create buildings using lots-mode tessellation + hierarchical placement
    for (const patch of outsidePatches) {
      // Skip farms only - allow residential buildings to coexist with slums
      if (patch.ward instanceof Farm) continue;
      
      let ward = patch.ward;
      if (!ward) { ward = new Ward(this, patch, 'residential'); patch.ward = ward; }
      
      // If patch has a Slum ward, add residential buildings to the slum's geometry
      const isSlum = patch.ward instanceof Slum;
      
      // If shantytown alleys exist, use hierarchical placement with lots-mode tessellation
      if (hasShantytownAlleys) {
        // Get all streets (non-alley roads) and alleys
        const streets = this.exteriorRoads.filter(r => !r.isAlley);
        const alleys = this.exteriorRoads.filter(r => r.isAlley);
        
        // Generate buildings using lots-mode tessellation via temporary Slum helper
        // (Slum class has the shrinkPolygon and createAlleys methods we need)
        const tempSlum = new Slum(this, patch);
        const shrunkShape = tempSlum.shrinkPolygon(patch.shape, 2);
        const allBuildings = tempSlum.createAlleys(shrunkShape, 10, 0.12, 0.3, Random.chance(0.3));
        const buildings = [];
        
        // Filter buildings using hierarchical street/alley proximity
        for (const building of allBuildings) {
          const bCenter = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
          bCenter.x /= building.length;
          bCenter.y /= building.length;
          
          // Check collision with alleys
          let tooCloseToAlley = false;
          let minAlleyDist = Infinity;
          for (const alley of alleys) {
            for (let j = 0; j < alley.length - 1; j++) {
              const dist = this.pointToSegmentDistance(bCenter, alley[j], alley[j + 1]);
              if (dist < minAlleyDist) minAlleyDist = dist;
              if (dist < alleyWidth * 1.2) {
                tooCloseToAlley = true;
                break;
              }
            }
            if (tooCloseToAlley) break;
          }
          
          // Check collision with streets
          let tooCloseToStreet = false;
          let minStreetDist = Infinity;
          for (const street of streets) {
            for (let j = 0; j < street.length - 1; j++) {
              const dist = this.pointToSegmentDistance(bCenter, street[j], street[j + 1]);
              if (dist < minStreetDist) minStreetDist = dist;
              if (dist < alleyWidth * 2.0) {
                tooCloseToStreet = true;
                break;
              }
            }
            if (tooCloseToStreet) break;
          }
          
          // Check water collision
          let inWater = false;
          if (Array.isArray(this.waterBodies)) {
            for (const water of this.waterBodies) {
              if (water && water.length >= 3 && pointInPoly(bCenter, water)) {
                inWater = true;
                break;
              }
            }
          }
          
          if (tooCloseToAlley || tooCloseToStreet || inWater) continue;
          
          // Apply hierarchical street proximity filtering
          // Priority 1: Near streets (primary)
          // Priority 2: Near alleys close to streets (secondary) 
          // Priority 3: Near alleys far from streets (tertiary)
          
          // INVERSE SQUARE ROOT BOOST: Buildings near city get massive density increase
          const cityCenter = Polygon.centroid(this.borderShape || patch.shape);
          const distFromCityCenter = Math.hypot(bCenter.x - cityCenter.x, bCenter.y - cityCenter.y);
          const distFromCityEdge = Math.max(1, distFromCityCenter - this.cityRadius);
          const cityDistBoost = 1.0 / Math.sqrt(distFromCityEdge);
          
          const streetThreshold = alleyWidth * 15;
          const alleyThreshold = alleyWidth * 8;
          let placementProbability = 0;
          
          // Priority 1: Building is near a street directly
          if (minStreetDist < streetThreshold) {
            const streetProximity = 1 - (minStreetDist / streetThreshold);
            placementProbability = Math.pow(streetProximity, 0.3) * 0.8 * cityDistBoost;
          }
          // Priority 2 & 3: Building is near an alley
          else if (minAlleyDist < alleyThreshold) {
            // Find closest street to the nearest alley point
            let alleyToStreetDist = Infinity;
            for (const alley of alleys) {
              for (const pt of alley) {
                const distFromBuilding = Math.hypot(pt.x - bCenter.x, pt.y - bCenter.y);
                if (distFromBuilding < minAlleyDist + 5) { // Within relevant range
                  for (const street of streets) {
                    for (let j = 0; j < street.length - 1; j++) {
                      const dist = this.pointToSegmentDistance(pt, street[j], street[j + 1]);
                      if (dist < alleyToStreetDist) alleyToStreetDist = dist;
                    }
                  }
                }
              }
            }
            
            if (alleyToStreetDist < alleyWidth * 20) {
              // Priority 2: Alley is close to streets
              const alleyStreetProximity = 1 - Math.min(1, alleyToStreetDist / (alleyWidth * 20));
              const alleyProximity = 1 - (minAlleyDist / alleyThreshold);
              placementProbability = Math.pow(alleyStreetProximity, 0.5) * alleyProximity * 0.5 * cityDistBoost;
            } else {
              // Priority 3: Alley is far from streets
              const alleyProximity = 1 - (minAlleyDist / alleyThreshold);
              placementProbability = alleyProximity * 0.2 * cityDistBoost;
            }
          }
          
          // Apply sparse placement multiplier + 200% overall density boost
          if (Random.float() < placementProbability * 1.2) {
            buildings.push(building);
          }
        }
        
        ward.geometry = buildings;
      } else {
        // No shantytown alleys - use traditional strip buildings along roads
        const buildings = ward.geometry || [];
        for (const road of this.exteriorRoads) {
          // Precompute total length for tapering from gate outward
          let totalLen = 0; const segLens = [];
          for (let i=0;i<road.length-1;i++){ const a=road[i], b=road[i+1]; const L=Math.hypot(b.x-a.x,b.y-a.y); segLens.push(L); totalLen+=L; }
          let acc = 0;
          for (let i=0;i<road.length-1;i++){
            const a = road[i], b = road[i+1];
            const L = segLens[i] || Math.hypot(b.x-a.x,b.y-a.y);
            // Taper depth: strong near city, fades outward; none after 60% of the road
            const t0 = acc/Math.max(1e-6,totalLen);
            const t1 = (acc+L)/Math.max(1e-6,totalLen);
            const tMid = (t0+t1)/2;
            // Depth scale: 1 at start, 0 at >=0.6
            const depthScale = Math.max(0, 1 - tMid/0.6);
            acc += L;
            // Quick reject by midpoint if far
            const mid = new Point((a.x+b.x)/2, (a.y+b.y)/2);
            const inOrNear = pointInPoly(mid, patch.shape);
            if (!inOrNear) {
              // Still might cross: check any endpoint inside
              if (!pointInPoly(a, patch.shape) && !pointInPoly(b, patch.shape)) {
                // As last resort, if segment intersects polygon, we'll clip accordingly below
              }
            }
            const insideSegs = segmentClipToPoly(a,b,patch.shape);
            for (const seg of insideSegs){
              const [p0,p1] = seg;
              if (depthScale <= 0.05) continue; // too far from gate
              const rows = makeStripBuildings(p0,p1, depthScale);
              buildings.push(...rows);
            }
          }
        }
        
        // Filter out buildings that intersect water bodies
        if (buildings.length > 0 && Array.isArray(this.waterBodies) && this.waterBodies.length > 0) {
          ward.geometry = buildings.filter(building => {
            if (!building || building.length < 3) return false;
            const center = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
            center.x /= building.length;
            center.y /= building.length;
            
            for (const water of this.waterBodies) {
              if (!water || water.length < 3) continue;
              if (pointInPoly(center, water)) return false;
            }
            return true;
          });
        } else {
          ward.geometry = buildings;
        }
      }
    }
  }
}

// ============================================================================
// Rendering
// ============================================================================

class Palette {
  static paper = '#F3EDE2';
  static light = '#C9B896';  // Definite tan/brown - no pink possible
  static dark = '#2B2416';
  static roof = '#8B7355'; // Brown roof colour
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
    // District label bounding boxes for collision avoidance (reset every render pass)
    this.labelBBoxes = [];
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
    
    // Use light brown terrain colour for background instead of white
    ctx.fillStyle = 'hsl(85, 30%, 80%)';
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

    // Terrain + city floor base layers (behind wards/buildings)
    this.drawOutsideTerrain(ctx);
    this.drawCityFloor(ctx);
    
    // Prepare city data for FormalMap
    const cityData = this.prepareCityData();
    
    // Create or update FormalMap (recreate if settings changed)
    if (!this.formalMap || this.settingsChanged()) {
      // Pass border shape to enable inside/outside clipping in PatchView
      this.formalMap = new FormalMap(cityData, Palette);
      this.formalMap.settings.interiorClip = this.model.borderShape;
      this.lastSettings = {
        streetWidth: StateManager.streetWidth,
        buildingGap: StateManager.buildingGap,
        wallThickness: StateManager.wallThickness
      };
    } else {
      // Update settings on existing FormalMap and propagate to child views
      this.formalMap.settings.wallThickness = StateManager.wallThickness;
      this.formalMap.settings.streetWidth = StateManager.streetWidth;
      this.formalMap.settings.buildingGap = StateManager.buildingGap;
      if (this.formalMap.walls) {
        this.formalMap.walls.settings = this.formalMap.settings;
      }
    }
    
    // Draw using view architecture
    this.formalMap.draw(ctx, {
      showBuildings: StateManager.showBuildings,
      showFarms: StateManager.showBuildings,
      showRoads: StateManager.showStreets,
      showWalls: StateManager.wallsNeeded,
      showMajorRoads: StateManager.showStreets,
      showMinorRoads: StateManager.showStreets,
      showTowers: StateManager.wallsNeeded,
      showGates: StateManager.wallsNeeded,
      showFocus: StateManager.showFocus || false,
      showCellOutlines: StateManager.showCellOutlines
    });
    
    // Draw water bodies AFTER walls/wards so they appear on top
    if (StateManager.showWater && this.model.waterBodies) {
      this.drawWaterBodies(ctx, this.model.waterBodies);
    }

    // Draw bridges on top of water/roads
    if (this.model.bridges && this.model.bridges.length > 0) {
      this.drawBridges(ctx, this.model.bridges);
    }
    
    // Draw piers
    if (this.model.piers && this.model.piers.length > 0) {
      this.drawPiers(ctx, this.model.piers);
    }
    
    // Draw waterfront features (docks, poles, boats)
    if (this.model.waterfrontBuildings && this.model.waterfrontBuildings.length > 0) {
      this.drawWaterfrontFeatures(ctx, this.model.waterfrontBuildings);
    }
    
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
        if (patch === this.model.plaza) {
          this.drawLabel(ctx, patch, 'Plaza');
        } else if (patch === this.model.citadel) {
          // Always label the citadel as such
          this.drawLabel(ctx, patch, 'Citadel');
        } else if (patch.ward) {
          this.drawLabel(ctx, patch, patch.ward.getLabel());
        }
      }
    }
    
    // Draw district names with curved text (reset collision store each frame)
    if (StateManager.showRegionNames && this.model.districts) {
      this.labelBBoxes = [];
      for (const district of this.model.districts) {
        this.drawDistrictLabel(ctx, district);
      }
    }
    
    ctx.restore();
  }

  // Draw light beige floor inside the city walls ONLY
  drawCityFloor(ctx) {
    if (!this.model.borderShape || this.model.borderShape.length < 3) return;
    
    // Clip to interior of wall AND outside of castle areas
    ctx.save();
    
    // Create compound clip path: inside city walls but outside castles
    const castles = this.model.patches.filter(p => p.ward instanceof Castle && p.ward.citadelWall && p.ward.citadelWall.length > 0);
    
    if (castles.length > 0) {
      // Use evenodd: city wall interior minus castle areas
      ctx.beginPath();
      ctx.moveTo(this.model.borderShape[0].x, this.model.borderShape[0].y);
      for (let i = 1; i < this.model.borderShape.length; i++) {
        ctx.lineTo(this.model.borderShape[i].x, this.model.borderShape[i].y);
      }
      ctx.closePath();
      // Subtract each castle area
      for (const patch of castles) {
        ctx.moveTo(patch.ward.citadelWall[0].x, patch.ward.citadelWall[0].y);
        for (let i = 1; i < patch.ward.citadelWall.length; i++) {
          ctx.lineTo(patch.ward.citadelWall[i].x, patch.ward.citadelWall[i].y);
        }
        ctx.closePath();
      }
      try { ctx.clip('evenodd'); } catch { ctx.clip(); }
    } else {
      // No castles, just clip to city wall interior
      ctx.beginPath();
      ctx.moveTo(this.model.borderShape[0].x, this.model.borderShape[0].y);
      for (let i = 1; i < this.model.borderShape.length; i++) {
        ctx.lineTo(this.model.borderShape[i].x, this.model.borderShape[i].y);
      }
      ctx.closePath();
      ctx.clip();
    }
    
    // Only draw for INSIDE patches - iterate through and fill each one
    for (const patch of this.model.patches) {
      if (!patch.withinCity) continue; // Skip outside patches
      if (patch.ward instanceof Castle) continue; // Skip castle patches
      if (!patch.shape || patch.shape.length < 3) continue;
      
      ctx.beginPath();
      ctx.moveTo(patch.shape[0].x, patch.shape[0].y);
      for (let i = 1; i < patch.shape.length; i++) {
        ctx.lineTo(patch.shape[i].x, patch.shape[i].y);
      }
      ctx.closePath();
      ctx.fillStyle = '#E8DCC8'; // light tan/beige base for all inside cells (no pink)
      ctx.fill();
    }
    
    ctx.restore();
  }

  // Shade ALL outside patches (cells) with green/brown natural variation, plus castle grounds
  drawOutsideTerrain(ctx) {
    if (!this.model || !this.model.patches) return;
    const noiseScale = 0.05;
    
    // Get outside patches
    const outsidePatches = this.model.patches.filter(p => 
      (!p.withinCity || p.ward instanceof Castle) && p.shape && p.shape.length >= 3
    );
    
    // Apply Urquhart graph to group adjacent patches by merging along removed edges
    const patchGroups = this.groupPatchesByUrquhart(outsidePatches);
    
    // Draw each group with unified color
    for (const group of patchGroups) {
      // Compute centroid of entire group for color
      let cx = 0, cy = 0, count = 0;
      for (const patch of group) {
        for (const p of patch.shape) {
          cx += p.x;
          cy += p.y;
          count++;
        }
      }
      if (count > 0) {
        cx /= count;
        cy /= count;
      }
      
      const n = (PerlinNoise.noise(cx * noiseScale, cy * noiseScale) + 1) * 0.5;
      
      // RGB blend between light green and light tan
      const r1 = 210, g1 = 220, b1 = 195;  // Light greenish
      const r2 = 205, g2 = 205, b2 = 170; // Light tan
      const r = Math.floor(r1 + (r2 - r1) * n);
      const g = Math.floor(g1 + (g2 - g1) * n);
      const b = Math.floor(b1 + (b2 - b1) * n);
      const fill = `rgb(${r}, ${g}, ${b})`;
      
      // Draw all patches in group with same color
      ctx.fillStyle = fill;
      for (const patch of group) {
        ctx.save();
        ctx.beginPath();
        ctx.moveTo(patch.shape[0].x, patch.shape[0].y);
        for (let i = 1; i < patch.shape.length; i++) {
          ctx.lineTo(patch.shape[i].x, patch.shape[i].y);
        }
        ctx.closePath();
        ctx.fill();
        ctx.restore();
      }
    }
  }
  
  groupPatchesByUrquhart(patches) {
    // Group patches, but limit group size to create moderate-sized fields
    const groups = [];
    const visited = new Set();
    const maxGroupSize = 5;  // Limit to small field groups
    
    for (const startPatch of patches) {
      if (visited.has(startPatch)) continue;
      
      const group = [];
      const queue = [startPatch];
      visited.add(startPatch);
      
      while (queue.length > 0 && group.length < maxGroupSize) {
        const patch = queue.shift();
        group.push(patch);
        
        // Find adjacent patches - only add if within group size limit
        if (group.length >= maxGroupSize) break;
        
        for (const otherPatch of patches) {
          if (visited.has(otherPatch)) continue;
          if (group.length >= maxGroupSize) break;
          
          // Check if patches share an edge
          if (this.patchesShareEdge(patch, otherPatch)) {
            visited.add(otherPatch);
            queue.push(otherPatch);
          }
        }
      }
      
      groups.push(group);
    }
    
    return groups;
  }
  
  patchesShareEdge(p1, p2) {
    // Check if two patches share a significant edge
    for (let i = 0; i < p1.shape.length; i++) {
      const a1 = p1.shape[i];
      const b1 = p1.shape[(i + 1) % p1.shape.length];
      
      for (let j = 0; j < p2.shape.length; j++) {
        const a2 = p2.shape[j];
        const b2 = p2.shape[(j + 1) % p2.shape.length];
        
        // Check if edges overlap (same points in reverse order)
        if ((Math.abs(a1.x - b2.x) < 0.1 && Math.abs(a1.y - b2.y) < 0.1 &&
             Math.abs(b1.x - a2.x) < 0.1 && Math.abs(b1.y - a2.y) < 0.1)) {
          return true;
        }
      }
    }
    return false;
  }
  
  /**
   * Prepare city data structure for view architecture
   */
  prepareCityData() {
    const wards = [];
    
    // Convert patches to ward data (include both inside and outside; rendering will clip appropriately)
    for (const patch of this.model.patches) {
      const isInside = !!patch.withinCity;
      const wardData = {
        shape: patch.shape,
        availableShape: patch.ward ? patch.ward.availableShape : null,
        colour: this.getPatchColour(patch),
        type: this.getPatchType(patch),
        buildings: [],
        furrows: null,
        inside: isInside,
        withinCity: isInside,
        ward: patch.ward,
        wardColourTint: this.getWardColourTint(patch.ward)
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
      // Bridges (from topology water-crossing edges)
      const bridges = (this.model.bridges || []).map(seg => ({ a: seg[0], b: seg[1] }));
    
    // Add exterior roads (preserve isAlley flag for rendering)
    if (this.model.exteriorRoads) {
      for (const road of this.model.exteriorRoads) {
        streets.push({
          path: road,
          major: false,
          isAlley: road.isAlley || false
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
          angle: Math.atan2(gate.y, gate.x)
        }))
      });
    }
    
    // Add citadel walls
    for (const patch of this.model.patches) {
      if (patch.ward instanceof Castle && patch.ward.citadelWall) {
        const castleGates = [];
        if (patch.ward.citadelGate) {
          castleGates.push({
            x: patch.ward.citadelGate.x,
            y: patch.ward.citadelGate.y,
            angle: 0
          });
        }
        walls.push({
          path: patch.ward.citadelWall,
          towers: this.generateWallTowers(patch.ward.citadelWall),
          gates: castleGates,
          isCitadel: true
        });
      }
    }
    
    return {
      wards: wards,
      streets: streets,
      walls: walls,
      bridges: bridges,
      settings: {
        streetWidth: (StateManager.streetWidth !== undefined) ? StateManager.streetWidth : 4.0,
        buildingGap: (StateManager.buildingGap !== undefined) ? StateManager.buildingGap : 1.8,
        wallThickness: (StateManager.wallThickness !== undefined) ? StateManager.wallThickness : 5,
        interiorClip: (this.model.borderShape && this.model.borderShape.length >= 3) ? this.model.borderShape : null
      }
    };
  }
  
  settingsChanged() {
    if (!this.lastSettings) return true;
    return (
      this.lastSettings.streetWidth !== StateManager.streetWidth ||
      this.lastSettings.buildingGap !== StateManager.buildingGap ||
      this.lastSettings.wallThickness !== StateManager.wallThickness
    );
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
          type: Random.chance(0.7) ? 'round' : 'square'
        });
        segmentDist += spacing;
      }
      
      distance += segmentLength;
    }
    
    return towers;
  }
  
  getPatchColour(patch) {
    if (patch === this.model.plaza || (patch.ward && patch.ward instanceof Plaza)) {
      return '#D4C5A0';
    } else if (patch === this.model.citadel) {
      return '#D5C8B8';
    } else if (patch.ward instanceof Farm) {
      // Use stored farm colour - beige/tan tones only
      if (!patch.ward.farmColor) {
        const hue = 35 + Random.float() * 15; // Beige to light brown range (35-50°)
        const sat = 22 + Random.float() * 10; // Low saturation for beige
        const light = 78 + Random.float() * 8; // Light tones
        patch.ward.farmColor = `hsl(${hue}, ${sat}%, ${light}%)`;
      }
      return patch.ward.farmColor;
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
    
    // Use light brown terrain colour for background instead of white
    ctx.fillStyle = 'hsl(85, 30%, 80%)';
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
    // City is centred at origin (0,0), no additional translation needed
    
    this.scale = scale;
    
    // Terrain + city floor base layers (behind patches/buildings)
    this.drawOutsideTerrain(ctx);
    this.drawCityFloor(ctx);
    
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
      // Draw ward geometry (buildings), clipping inside/outside depending on patch.withinCity
      // Skip castle buildings here, draw them later
      if (patch.ward && patch.ward.geometry && !(patch.ward instanceof Castle)) {
        const wardColourTint = this.getWardColourTint(patch.ward);
        this.drawBuildings(ctx, patch.ward.geometry, !!patch.withinCity, wardColourTint);
      }
    }
    
    // Draw castle floors
    for (const patch of this.model.patches) {
      if (patch.ward instanceof Castle && patch.ward.citadelWall && patch.ward.citadelWall.length > 0) {
        ctx.save();
        ctx.beginPath();
        ctx.moveTo(patch.ward.citadelWall[0].x, patch.ward.citadelWall[0].y);
        for (let i = 1; i < patch.ward.citadelWall.length; i++) {
          ctx.lineTo(patch.ward.citadelWall[i].x, patch.ward.citadelWall[i].y);
        }
        ctx.closePath();
        ctx.fillStyle = '#9a9a9a';
        ctx.fill();
        ctx.restore();
      }
    }
    
    // Draw citadel walls AFTER castle floor (only if walls enabled)
    if (StateManager.wallsNeeded) {
      for (const patch of this.model.patches) {
        if (patch.ward instanceof Castle) {
          this.drawCitadelWall(ctx, patch.ward);
        }
      }
    }
    
    for (const gate of this.model.gates) {
      this.drawGate(ctx, gate);
    }
    
    // Draw water bodies if enabled
    if (StateManager.showWater && this.model.waterBodies) {
      this.drawWaterBodies(ctx, this.model.waterBodies);
    }

    // Draw piers before bridges
    if (this.model.piers && this.model.piers.length > 0) {
      this.drawPiers(ctx, this.model.piers);
    }

    // Draw bridges on top of water/roads
    if (this.model.bridges && this.model.bridges.length > 0) {
      this.drawBridges(ctx, this.model.bridges);
    }
    
    // Draw waterfront features
    if (this.model.waterfrontBuildings && this.model.waterfrontBuildings.length > 0) {
      this.drawWaterfrontFeatures(ctx, this.model.waterfrontBuildings);
    }
    
    // Draw castle buildings AFTER floor, gates, water, and bridges
    for (const patch of this.model.patches) {
      if (patch.ward instanceof Castle && patch.ward.geometry) {
        const wardColourTint = this.getWardColourTint(patch.ward);
        this.drawBuildings(ctx, patch.ward.geometry, !!patch.withinCity, wardColourTint);
      }
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
    
    // Draw castle towers (gatehouses) AFTER EVERYTHING - on top with NO clipping (only if walls enabled)
    if (StateManager.wallsNeeded) {
      for (const patch of this.model.patches) {
        if (patch.ward instanceof Castle && patch.ward.towers) {
          const wardColourTint = this.getWardColourTint(patch.ward);
        // Direct draw without any clipping
        ctx.save();
        BuildingPainter.paint(ctx, patch.ward.towers, Palette.roof, Palette.dark, 0.5, this.scale, wardColourTint);
        ctx.restore();
        }
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
    
    // Draw district names with curved text (reset collision store each frame)
    if (StateManager.showRegionNames && this.model.districts) {
      this.labelBBoxes = [];
      for (const district of this.model.districts) {
        this.drawDistrictLabel(ctx, district);
      }
    }
    
    ctx.restore();
  }
  
  drawWaterfrontFeatures(ctx, features) {
    const safeScale = Math.max(1e-3, this.scale || 1);
    ctx.save();
    
    for (const {feature, geometry} of features) {
      if (feature === 'dock' && Array.isArray(geometry)) {
        // Draw dock as a wooden platform
        ctx.fillStyle = '#8B7355';
        ctx.strokeStyle = Palette.dark;
        ctx.lineWidth = Math.max(0.3 / safeScale, 0.5);
        ctx.beginPath();
        ctx.moveTo(geometry[0].x, geometry[0].y);
        for (let i = 1; i < geometry.length; i++) {
          ctx.lineTo(geometry[i].x, geometry[i].y);
        }
        ctx.closePath();
        ctx.fill();
        ctx.stroke();
      } else if (feature === 'post' && geometry.x !== undefined) {
        // Draw mooring post
        ctx.fillStyle = '#5C4033';
        ctx.strokeStyle = Palette.dark;
        ctx.lineWidth = Math.max(0.2 / safeScale, 0.3);
        ctx.beginPath();
        ctx.arc(geometry.x, geometry.y, Math.max(0.4 / safeScale, 0.6), 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
      } else if (feature === 'boat' && Array.isArray(geometry)) {
        // Draw small boat
        ctx.fillStyle = '#6B4423';
        ctx.strokeStyle = Palette.dark;
        ctx.lineWidth = Math.max(0.2 / safeScale, 0.4);
        ctx.beginPath();
        ctx.moveTo(geometry[0].x, geometry[0].y);
        for (let i = 1; i < geometry.length; i++) {
          ctx.lineTo(geometry[i].x, geometry[i].y);
        }
        ctx.closePath();
        ctx.fill();
        ctx.stroke();
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
    // Allow opting into Poisson trees explicitly; keep legacy sparse trees by default
    if (StateManager.treeMode === 'poisson') {
      const trees = [];
      const cityRadius = this.model.cityRadius;
      const savedSeed = Random.seed;
      const farmPolys = this.model.patches.filter(p => p.ward instanceof Farm).map(p => p.shape);
      const pointSegDist = (p, a, b) => {
        const abx=b.x-a.x, aby=b.y-a.y; const apx=p.x-a.x, apy=p.y-a.y; const ab2=abx*abx+aby*aby||1e-6; let t=(apx*abx+apy*aby)/ab2; t=Math.max(0,Math.min(1,t)); const x=a.x+abx*t, y=a.y+aby*t; return Math.hypot(p.x-x,p.y-y);
      };
      const pointPolyDist = (p, poly) => {
        let best=Infinity; for (let i=0;i<poly.length;i++){const a=poly[i], b=poly[(i+1)%poly.length]; best=Math.min(best, pointSegDist(p,a,b));} return best;
      };
      const inAnyWater = (pt) => {
        if (!this.model.waterBodies || this.model.waterBodies.length === 0) return false;
        for (const w of this.model.waterBodies) { if (w && w.length>=3 && this.isPointInPolygon(pt,w)) return true; } return false;
      };
      for (const patch of this.model.patches) {
        const ward = patch.ward; if (!ward || !patch.shape || patch.shape.length<3) continue;
        const patchCenter = Polygon.centroid(patch.shape);
        const distCenter = Math.hypot(patchCenter.x, patchCenter.y);
        const norm = distCenter / cityRadius;
        let base = 4.0; if (ward instanceof Park) base = 2.8; else if (ward instanceof Farm) base = 6.5; else if (ward instanceof Market || ward instanceof Cathedral) base = 5.2; else if (ward instanceof Castle) base = 6.8;
        const falloff = 0.8*norm; const spacing0 = base * (1.0 + falloff);
        const densityFn = (p)=>{
          const n = (PerlinNoise.noise(p.x*0.06, p.y*0.06)+1)*0.5; let local = spacing0 * (0.85 + 0.5*n);
          if (!(ward instanceof Farm) && farmPolys.length>0){ let nearest = Infinity; for (const f of farmPolys){ nearest = Math.min(nearest, pointPolyDist(p,f)); if (nearest<6) break; } if (isFinite(nearest) && nearest < 12) local *= (0.95 + 0.1*(nearest/12)); }
          if (ward instanceof Farm){ const db = pointPolyDist(p, patch.shape); if (db < 8) local *= (0.8 + 0.4*(db/8)); else local *= 1.8; }
          return local;
        };
        const poly = (patch.ward && patch.ward.availableShape && patch.ward.availableShape.length>=3) ? patch.ward.availableShape : patch.shape;
        const points = CityRenderer.poissonSample(poly, densityFn, 30);
        for (const point of points) {
          if (inAnyWater(point)) continue;
          let ok = true; if (ward.geometry) { for (const building of ward.geometry) { const polyB = Array.isArray(building) ? building : (building && building.points ? building.points : null); if (polyB && polyB.length>=3 && this.isPointInPolygon(point, polyB)) { ok = false; break; } } }
          if (!ok) continue;
          trees.push({ pos: point, crown: this.getTreeCrown() });
        }
      }
      Random.seed = savedSeed; return trees;
    }

    // Legacy sparse trees: grid+jitter with low density
    const trees = [];
    const inAnyWater = (pt) => {
      if (!this.model.waterBodies || this.model.waterBodies.length === 0) return false;
      for (const w of this.model.waterBodies) { if (w && w.length>=3 && this.isPointInPolygon(pt,w)) return true; } return false;
    };
    for (const patch of this.model.patches) {
      const ward = patch.ward; if (!ward || !patch.shape || patch.shape.length<3) continue;
      // Suppress most trees on outer blank wards (outside walls & not park/farm)
      const outside = !patch.withinCity;
      const isPark = ward instanceof Park; const isFarm = ward instanceof Farm;
      if (outside && !isPark && !isFarm) {
        // Skip entirely to avoid cluttering outer blanks
        continue;
      }
      const spacing = isPark ? 3.2 : (isFarm ? 8.0 : 7.0);
      const baseDensity = isPark ? 0.55 : (isFarm ? 0.06 : 0.18);
      const density = outside ? baseDensity * 0.3 : baseDensity; // lighter just outside walls if allowed (parks/farms)
      const candidates = this.fillAreaWithTreePattern(patch.shape, spacing, density);
      for (const point of candidates) {
        if (inAnyWater(point)) continue;
        let ok = true; if (ward.geometry) { for (const building of ward.geometry) { const polyB = Array.isArray(building) ? building : (building && building.points ? building.points : null); if (polyB && polyB.length>=3 && this.isPointInPolygon(point, polyB)) { ok = false; break; } } }
        if (!ok) continue;
        trees.push({ pos: point, crown: this.getTreeCrown() });
      }
    }
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

  // Bridson Poisson-disk sampling within a polygon with variable spacing.
  // densityFn returns local minimal spacing (radius) at a point.
  static poissonSample(polygon, densityFnOrR, k = 30) {
    const rAt = (p) => (typeof densityFnOrR === 'function' ? Math.max(0.8, densityFnOrR(p)) : Math.max(0.8, densityFnOrR));
    // Bounding box
    let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity; for(const v of polygon){minX=Math.min(minX,v.x);minY=Math.min(minY,v.y);maxX=Math.max(maxX,v.x);maxY=Math.max(maxY,v.y);}    
    // Use conservative smallest cell for grid based on min r in bbox corners
    const sampleR = (x,y)=>rAt(new Point(x,y));
    const rmin = Math.max(0.8, Math.min(sampleR(minX,minY), sampleR(maxX,maxY), sampleR(minX,maxY), sampleR(maxX,minY)));
    const cell = rmin/Math.SQRT2;
    const cols = Math.ceil((maxX-minX)/cell)+1, rows = Math.ceil((maxY-minY)/cell)+1;
    const grid = new Array(cols*rows).fill(null);
    const toIndex = (p)=>{const x=Math.floor((p.x-minX)/cell), y=Math.floor((p.y-minY)/cell); return y*cols+x;};
    const inPoly = (pt)=>{ let inside=false; for(let i=0,j=polygon.length-1;i<polygon.length;j=i++){const xi=polygon[i].x, yi=polygon[i].y, xj=polygon[j].x, yj=polygon[j].y; const inter=((yi>pt.y)!=(yj>pt.y)) && (pt.x < (xj-xi)*(pt.y-yi)/(yj-yi)+xi); if (inter) inside=!inside;} return inside; };
    const samples = []; const active = [];
    // initial sample
    let tries = 0; while(tries++<50){ const p = new Point(minX + Random.float()*(maxX-minX), minY + Random.float()*(maxY-minY)); if (inPoly(p)) { samples.push(p); active.push(p); grid[toIndex(p)] = p; break; }}
    if (samples.length===0) return samples;
    while(active.length){ const idx = Random.int(0, active.length); const s = active[idx]; const r = rAt(s); let placed=false; for (let i=0;i<k;i++){ const ang = Random.float()*Math.PI*2; const mag = r*(1 + Random.float()); const p = new Point(s.x + Math.cos(ang)*mag, s.y + Math.sin(ang)*mag); if (!inPoly(p)) continue; const rad = rAt(p); const gx = Math.floor((p.x-minX)/cell), gy = Math.floor((p.y-minY)/cell); let ok=true; for(let yy=Math.max(0,gy-2); yy<=Math.min(rows-1,gy+2) && ok; yy++){ for(let xx=Math.max(0,gx-2); xx<=Math.min(cols-1,gx+2) && ok; xx++){ const q = grid[yy*cols+xx]; if(!q) continue; if (Point.distance(p,q) < Math.min(rad, rAt(q))) ok=false; }} if(!ok) continue; samples.push(p); active.push(p); grid[toIndex(p)]=p; placed=true; break; } if(!placed){ active.splice(idx,1); } }
    return samples;
  }

  getTreeCrown() {
    // Generate a random tree crown polygon 
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
    
    // Use the ward's inset shape if available (respects walls/water), otherwise use patch shape
    const shapeToRender = (patch.ward && patch.ward.availableShape && patch.ward.availableShape.length >= 3) 
      ? patch.ward.availableShape 
      : patch.shape;

    // PREPASS: For inside patches near the city wall, paint the whole patch with
    // the outside terrain colour BEFORE any clipping, so any slivers that extend
    // outside the wall get covered with green/brown. We'll then overdraw beige
    // after we set the interior clip below.
    if (patch.withinCity && this.model.borderShape && this.model.borderShape.length >= 3) {
      // Compute centroid
      let cx0 = 0, cy0 = 0; for (const p of shapeToRender) { cx0 += p.x; cy0 += p.y; } cx0 /= shapeToRender.length; cy0 /= shapeToRender.length;
      // Distance from centroid to wall edges
      let minDist0 = Infinity;
      for (let i = 0; i < this.model.borderShape.length; i++) {
        const a = this.model.borderShape[i];
        const b = this.model.borderShape[(i + 1) % this.model.borderShape.length];
        const abx = b.x - a.x, aby = b.y - a.y; const apx = cx0 - a.x, apy = cy0 - a.y;
        const ab2 = abx*abx + aby*aby || 1e-6; let t = (apx*abx + apy*aby) / ab2; t = Math.max(0, Math.min(1, t));
        const px = a.x + abx*t, py = a.y + aby*t; const d = Math.hypot(cx0 - px, cy0 - py);
        if (d < minDist0) minDist0 = d;
      }
      const isEdgeInside = minDist0 < 8; // threshold in map units
      if (isEdgeInside) {
        // Outside terrain colour using Perlin noise at centroid (beige/tan tones)
        const n = (PerlinNoise.noise(cx0 * 0.05, cy0 * 0.05) + 1) * 0.5;
        const h = 85 * (1 - n) + 40 * n;  // Green to beige/tan (no pink)
        const s = 30 * (1 - n) + 28 * n;  // Lower saturation
        const l = 80 * (1 - n) + 83 * n;
        ctx.save();
        ctx.beginPath();
        ctx.moveTo(shapeToRender[0].x, shapeToRender[0].y);
        for (let i = 1; i < shapeToRender.length; i++) ctx.lineTo(shapeToRender[i].x, shapeToRender[i].y);
        ctx.closePath();
        ctx.fillStyle = `hsl(${h.toFixed(0)}, ${s.toFixed(0)}%, ${l.toFixed(0)}%)`;
        ctx.fill();
        ctx.restore();
      }
    }

    // Clip to walls: interior for inside-city patches, exterior for outside-city patches
    let clipped = false;
    if (this.model.borderShape && this.model.borderShape.length >= 3) {
      clipped = true;
      ctx.save();
      ctx.beginPath();
      if (patch.withinCity) {
        ctx.moveTo(this.model.borderShape[0].x, this.model.borderShape[0].y);
        for (let i = 1; i < this.model.borderShape.length; i++) {
          ctx.lineTo(this.model.borderShape[i].x, this.model.borderShape[i].y);
        }
        ctx.closePath();
        ctx.clip();
      } else {
        const M = 1e5;
        ctx.moveTo(-M, -M);
        ctx.lineTo(M, -M);
        ctx.lineTo(M, M);
        ctx.lineTo(-M, M);
        ctx.closePath();
        ctx.moveTo(this.model.borderShape[0].x, this.model.borderShape[0].y);
        for (let i = 1; i < this.model.borderShape.length; i++) {
          ctx.lineTo(this.model.borderShape[i].x, this.model.borderShape[i].y);
        }
        ctx.closePath();
        try { ctx.clip('evenodd'); } catch { ctx.clip(); }
      }
    }
    // Fill logic
    if (!patch.withinCity) {
      // Outside city: skip (base terrain layer already draws these)
    } else if (patch.ward instanceof Castle) {
      // Castle: skip, let terrain colour show through (castle has its own wall)
    } else if (patch === this.model.plaza || (patch.ward && patch.ward instanceof Plaza)) {
      ctx.fillStyle = '#D4C5A0'; // More distinct tan/sand colour for central plaza
      ctx.fill();
    } else if (patch === this.model.citadel) {
      ctx.fillStyle = '#C8BCA8';  // Tan/grey for citadel (no pink)
      ctx.fill();
    } else if (patch.ward instanceof Farm) {
      // Different pale beige/tan for each farm
      if (!patch.ward.farmColor) {
        const hue = 35 + Random.float() * 15; // Beige to light brown range (35-50°)
        const sat = 22 + Random.float() * 10; // Low saturation for beige
        const light = 78 + Random.float() * 8; // Light tones
        patch.ward.farmColor = `hsl(${hue}, ${sat}%, ${light}%)`;
      }
      ctx.fillStyle = patch.ward.farmColor;
      ctx.fill();
    } else {
      // Standard inside ward: no additional fill here; beige base (drawn elsewhere)
      // will cover interior due to the interior clip above. Any slivers outside
      // the wall were pre-painted in the PREPASS when near the wall.
    }
    
    // Draw farm details AFTER fill, within cell bounds
    if (patch.ward instanceof Farm) {
      this.drawFarmDetails(ctx, patch.ward, patch.shape);
    }
    
    // Draw cell boundaries if option enabled
    if (StateManager.showCellOutlines) {
      const safeScale = Math.max(1e-3, this.scale || 1);
      ctx.strokeStyle = Palette.light + '30';
      ctx.lineWidth = Math.min(6, 1 / safeScale);
      ctx.stroke();
    }

    if (clipped) ctx.restore();
  }

  drawWall(ctx, wall) {
    if (wall.length === 0) return;

    const gates = this.model.gates || [];
    const safeScale = Math.max(1e-3, this.scale || 1);
    const wallThickness = (StateManager.wallThickness || 2) / safeScale;

    ctx.save();
    
    // Clip to OUTSIDE castle areas before drawing city wall
    const castles = this.model.patches.filter(p => p.ward instanceof Castle && p.ward.citadelWall && p.ward.citadelWall.length > 0);
    if (castles.length > 0) {
      const M = 1e5;
      ctx.beginPath();
      // Big outer rect
      ctx.moveTo(-M, -M);
      ctx.lineTo(M, -M);
      ctx.lineTo(M, M);
      ctx.lineTo(-M, M);
      ctx.closePath();
      // Subtract each castle area
      for (const patch of castles) {
        ctx.moveTo(patch.ward.citadelWall[0].x, patch.ward.citadelWall[0].y);
        for (let i = 1; i < patch.ward.citadelWall.length; i++) {
          ctx.lineTo(patch.ward.citadelWall[i].x, patch.ward.citadelWall[i].y);
        }
        ctx.closePath();
      }
      try { ctx.clip('evenodd'); } catch { ctx.clip(); }
    }

    ctx.strokeStyle = Palette.dark;
    ctx.lineWidth = wallThickness;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';

    // Draw the complete wall (now clipped to outside castles)
    ctx.beginPath();
    ctx.moveTo(wall[0].x, wall[0].y);
    for (let i = 1; i < wall.length; i++) {
      ctx.lineTo(wall[i].x, wall[i].y);
    }
    ctx.closePath();
    ctx.stroke();
    
    ctx.restore();

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

    // Erase wall where it crosses water bodies to create river/coast gaps
    if (this.model.waterBodies && this.model.waterBodies.length > 0) {
      for (const water of this.model.waterBodies) {
        if (!water || water.length < 3) continue;
        ctx.save();
        ctx.globalCompositeOperation = 'destination-out';
        // Clip to water polygon
        ctx.beginPath();
        ctx.moveTo(water[0].x, water[0].y);
        for (let i = 1; i < water.length; i++) ctx.lineTo(water[i].x, water[i].y);
        ctx.closePath();
        ctx.clip();

        // Stroke along wall path inside water to carve a gap
        ctx.strokeStyle = 'black';
        ctx.lineWidth = wallThickness * 2.2; // slightly larger than wall
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        ctx.beginPath();
        ctx.moveTo(wall[0].x, wall[0].y);
        for (let i = 1; i < wall.length; i++) ctx.lineTo(wall[i].x, wall[i].y);
        ctx.closePath();
        ctx.stroke();
        ctx.restore();
      }
    }

    // Watergates: draw piers where wall intersects water
    if (this.model.waterBodies && this.model.waterBodies.length > 0) {
      const drawPiersAt = (p0, p1) => {
        // Vector and safe length
        const vx = p1.x - p0.x, vy = p1.y - p0.y;
        const len = Math.hypot(vx, vy);
        if (!isFinite(len) || len <= 1e-6) return; // nothing to draw
        const ux = vx / len, uy = vy / len; const nx = -uy, ny = ux;

        // Robust sizing with clamps to avoid 0 or Infinity
        const safeScale = Math.max(1e-3, this.scale || 1);
        const baseThick = Math.max(0.5, (StateManager.wallThickness || 2));
        const pierLen = Math.max(0.6 / safeScale, (baseThick * 1.2) / safeScale);
        const spacing = Math.max(0.8 / safeScale, pierLen * 1.6);

        // Count must be a finite integer and reasonably bounded
        let count = Math.floor(len / spacing);
        if (!isFinite(count) || count < 2) count = 2;
        count = Math.min(count, 200); // hard cap to prevent runaway loops

        ctx.save();
        ctx.strokeStyle = Palette.dark;
        ctx.lineWidth = Math.max(0.6 / safeScale, 0.6);
        for (let i = 0; i <= count; i++) {
          const t = i / count;
          const x = p0.x + vx * t, y = p0.y + vy * t;
          ctx.beginPath();
          ctx.moveTo(x, y);
          ctx.lineTo(x + nx * pierLen, y + ny * pierLen);
          ctx.stroke();
        }
        ctx.restore();
      };
      // Find intersections between wall segments and each water polygon
      for (let i = 0; i < wall.length; i++) {
        const a = wall[i]; const b = wall[(i+1)%wall.length];
        for (const water of this.model.waterBodies) {
          for (let j=0;j<water.length;j++){
            const c = water[j], d = water[(j+1)%water.length];
            const r = {x: b.x - a.x, y: b.y - a.y};
            const s = {x: d.x - c.x, y: d.y - c.y};
            const denom = r.x * s.y - r.y * s.x; if (Math.abs(denom) < 1e-8) continue;
            const t = ((c.x - a.x) * s.y - (c.y - a.y) * s.x) / denom;
            const u = ((c.x - a.x) * r.y - (c.y - a.y) * r.x) / denom;
            if (t >= 0 && t <= 1 && u >= 0 && u <= 1) {
              // Draw a short pier segment centered around intersection along the wall direction
              const mid = new Point(a.x + r.x * t, a.y + r.y * t);
              const rlen = Math.hypot(r.x, r.y) || 1e-6;
              const ux = r.x / rlen, uy = r.y / rlen; // wall tangent
              const nx = -uy, ny = ux; // outward normal (both sides visually ok)
              const segHalf = Math.min(3 / this.scale, 0.5 * rlen);
              const p0 = new Point(mid.x - ux * segHalf, mid.y - uy * segHalf);
              const p1 = new Point(mid.x + ux * segHalf, mid.y + uy * segHalf);
              drawPiersAt(p0, p1);

              // Distinct watergate treatment by water type
              if (this.model.riverType === 'canal') {
                // Stone arch over the gap
                const archR = Math.max(wallThickness * 1.1, 1.2 / this.scale);
                const theta0 = Math.atan2(ny, nx) - Math.PI * 0.5; // orient across wall
                ctx.save();
                ctx.strokeStyle = Palette.dark;
                ctx.lineWidth = Math.max(0.7 / this.scale, 0.7);
                ctx.beginPath();
                ctx.arc(mid.x, mid.y, archR, theta0, theta0 + Math.PI, false);
                ctx.stroke();
                ctx.restore();
              } else if (this.model.riverType === 'river') {
                // Wooden abutments/posts at the edges of the gap
                const postLen = Math.max(1.2 / this.scale, wallThickness * 0.8);
                const inset = Math.max(0.4 / this.scale, wallThickness * 0.5);
                const left = new Point(mid.x - ux * inset, mid.y - uy * inset);
                const right = new Point(mid.x + ux * inset, mid.y + uy * inset);
                ctx.save();
                ctx.strokeStyle = Palette.dark;
                ctx.lineWidth = Math.max(0.9 / this.scale, 0.9);
                ctx.beginPath();
                ctx.moveTo(left.x - nx * postLen, left.y - ny * postLen);
                ctx.lineTo(left.x + nx * postLen, left.y + ny * postLen);
                ctx.moveTo(right.x - nx * postLen, right.y - ny * postLen);
                ctx.lineTo(right.x + nx * postLen, right.y + ny * postLen);
                ctx.stroke();
                ctx.restore();
              }
            }
          }
        }
      }
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

  getWardColourTint(ward) {
    if (!ward) return null;
    
    const colours = {
      'castle': '#FFD700',    // Gold
      'cathedral': '#4169E1',      // Royal blue
      'temple': '#9370DB',         // Medium purple
      'market': '#faf0e4ff',          // Light beige
      'slum': '#535151',           // Dim grey
      'farm': '#D8C8A8',      // Light brown-green
      'park': '#C8D4A8',      // Light green
      'plaza': '#D4C5A0',     // Tan/sand
      'patriciate': '#FF1493',     // Deep pink
      'merchants': '#00CED1',      // Dark turquoise
      'craftsmen': '#3d303dff',      // Dark purple
      'residential': '#32CD32',    // Lime green
      'administration': '#FF0000', // Bright red
      'military': '#8B0000'        // Dark red
    };
    
    // Try class name first (normalized to lowercase)
    const wardClassName = ward.constructor.name.toLowerCase();
    if (colours[wardClassName]) {
      return colours[wardClassName];
    }
    
    // Fall back to wardType property (normalized to lowercase)
    if (ward.wardType) {
      const wardType = ward.wardType.toLowerCase();
      if (colours[wardType]) {
        return colours[wardType];
      }
    }
    
    return null;
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
    
    // Alleys are nearly invisible - just enough to affect building placement
    if (road.isAlley) {
      ctx.strokeStyle = Palette.dark + '10'; // 3% opacity - barely visible
      ctx.lineWidth = (StateManager.streetWidth * 0.03 || 0.1) / this.scale;
      ctx.lineCap = 'round';
      ctx.stroke();
    } else {
      // Regular roads are thicker and more visible than interior streets
      ctx.strokeStyle = Palette.dark + '80';
      ctx.lineWidth = (StateManager.streetWidth * 1.5 || 3.0) / this.scale;
      ctx.lineCap = 'round';
      ctx.stroke();
    }
  }

  drawBuildings(ctx, buildings, inside = true, wardType = null) {
    if (!StateManager.showBuildings) return;
    
    const gap = this.model.buildingGap; // Use full gap value in both modes
    const border = this.model.borderShape;
    let didClip = false;
    if (Array.isArray(border) && border.length >= 3) {
      didClip = true;
      ctx.save();
      ctx.beginPath();
      if (inside) {
        ctx.moveTo(border[0].x, border[0].y);
        for (let i = 1; i < border.length; i++) ctx.lineTo(border[i].x, border[i].y);
        ctx.closePath();
        ctx.clip();
      } else {
        const M = 1e5;
        ctx.moveTo(-M, -M);
        ctx.lineTo(M, -M);
        ctx.lineTo(M, M);
        ctx.lineTo(-M, M);
        ctx.closePath();
        ctx.moveTo(border[0].x, border[0].y);
        for (let i = 1; i < border.length; i++) ctx.lineTo(border[i].x, border[i].y);
        ctx.closePath();
        try { ctx.clip('evenodd'); } catch { ctx.clip(); }
      }
    }
    
    // Process buildings with gap if needed
    let processedBuildings = buildings;
    if (gap > 0) {
      processedBuildings = buildings.map(building => {
        if (!Array.isArray(building) || building.length === 0) return building;
        
        const center = building.reduce((acc, p) => ({x: acc.x + p.x, y: acc.y + p.y}), {x: 0, y: 0});
        center.x /= building.length;
        center.y /= building.length;
        // More aggressive shrink factor for better visual separation
        const shrinkFactor = 1 - Math.min(0.45, gap * 0.2);
        return building.map(p => new Point(
          center.x + (p.x - center.x) * shrinkFactor,
          center.y + (p.y - center.y) * shrinkFactor
        ));
      }).filter(b => Array.isArray(b) && b.length > 0);
    } else {
      processedBuildings = buildings.filter(b => Array.isArray(b) && b.length > 0);
    }
    
    // Use BuildingPainter for 3D rendering
    BuildingPainter.paint(ctx, processedBuildings, Palette.roof, Palette.dark, 0.5, this.scale, wardType);
    if (didClip) ctx.restore();
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
      const safeScale = Math.max(1e-3, this.scale || 1);
      ctx.strokeStyle = Palette.dark + '40'; // Semi-transparent dark lines
      ctx.lineWidth = Math.max(0.2, 0.3 / safeScale);
      
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
    const safeScale = Math.max(1e-3, this.scale || 1);
    const wallThickness = (StateManager.wallThickness || 5) / safeScale;
    const gateWidth = wallThickness * 1.6;
    const gateHeight = wallThickness * 2.4;
    
    ctx.save();
    ctx.translate(gate.x, gate.y);
    
    // Rotate gate to align with wall
    const angle = Math.atan2(gate.y, gate.x);
    ctx.rotate(angle);
    
    // Draw gate opening as rectangle
    ctx.fillStyle = Palette.paper;
    ctx.fillRect(-gateWidth / 2, -gateHeight / 2, gateWidth, gateHeight);
    
    // Gate outline
    ctx.strokeStyle = Palette.dark;
    ctx.lineWidth = Math.max(0.5, wallThickness * 0.15);
    ctx.strokeRect(-gateWidth / 2, -gateHeight / 2, gateWidth, gateHeight);
    
    ctx.restore();
  }
  
  drawBridges(ctx, bridges) {
    // Stone vs wooden style depending on canal/river type
    const isCanal = this.model && this.model.riverType === 'canal';
    const streetW = (StateManager.streetWidth || 2.0);
    const safeScale = Math.max(1e-3, this.scale || 1);
    let deckW = (isCanal ? 1.1 : 1.4) * streetW / safeScale;
    deckW = Math.min(deckW, 200); // cap absurd widths
    const outlineW = Math.min(deckW * (isCanal ? 0.18 : 0.32), 50);
    const plankSpacing = Math.max(1.2 / safeScale, deckW * 0.5);
    const abutLen = Math.max(1.5 / safeScale, deckW * (isCanal ? 0.5 : 0.7));

    ctx.save();
    ctx.lineCap = 'round';

    if (isCanal) {
      // Stone bridge: filled deck with subtle arch shadows
      for (const seg of bridges) {
        const a = seg[0] || seg.a, b = seg[1] || seg.b; if (!a || !b) continue;
        const vx=b.x-a.x, vy=b.y-a.y; const len=Math.hypot(vx,vy)||1e-6; const ux=vx/len, uy=vy/len; const nx=-uy, ny=ux;
        // Deck fill
        ctx.fillStyle = '#C8C5BE';
        ctx.beginPath();
        ctx.moveTo(a.x - nx*deckW*0.5, a.y - ny*deckW*0.5);
        ctx.lineTo(b.x - nx*deckW*0.5, b.y - ny*deckW*0.5);
        ctx.lineTo(b.x + nx*deckW*0.5, b.y + ny*deckW*0.5);
        ctx.lineTo(a.x + nx*deckW*0.5, a.y + ny*deckW*0.5);
        ctx.closePath(); ctx.fill();
        // Outline
        ctx.strokeStyle = Palette.dark + '90'; ctx.lineWidth = outlineW; ctx.beginPath();
        ctx.moveTo(a.x - nx*deckW*0.5, a.y - ny*deckW*0.5);
        ctx.lineTo(b.x - nx*deckW*0.5, b.y - ny*deckW*0.5);
        ctx.lineTo(b.x + nx*deckW*0.5, b.y + ny*deckW*0.5);
        ctx.lineTo(a.x + nx*deckW*0.5, a.y + ny*deckW*0.5); ctx.closePath(); ctx.stroke();
        // Simple arch hints (three semi-elliptic shadows)
        const arches = Math.max(1, Math.floor(len / (deckW*2.2)));
        ctx.strokeStyle = Palette.dark + '40'; ctx.lineWidth = Math.max(0.6/safeScale, outlineW*0.5);
        for (let i=0;i<arches;i++){
          const t = (i+0.5)/arches; const cx = a.x + vx*t; const cy = a.y + vy*t; const w = deckW*0.6; const h = deckW*0.35;
          // Draw arch as half-ellipse line across deck
          ctx.beginPath();
          for (let k=0;k<=8;k++){
            const ang = Math.PI * (k/8); // 0..PI
            const ex = cx + nx*(Math.cos(ang)*w*0.5) + ux*(Math.sin(ang)*w*0.05);
            const ey = cy + ny*(Math.cos(ang)*w*0.5) + uy*(Math.sin(ang)*h*0.4);
            if(k===0) ctx.moveTo(ex,ey); else ctx.lineTo(ex,ey);
          }
          ctx.stroke();
        }
      }
    } else {
      // Wooden style (existing behavior)
      ctx.strokeStyle = Palette.paper;
      ctx.lineWidth = Math.min(deckW, 100);
      for (const seg of bridges) {
        const a = seg[0] || seg.a, b = seg[1] || seg.b; if (!a || !b) continue;
        ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
      }
      ctx.strokeStyle = Palette.dark + '80';
      ctx.lineWidth = Math.min(outlineW, 50);
      for (const seg of bridges) {
        const a = seg[0] || seg.a, b = seg[1] || seg.b; if (!a || !b) continue;
        ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
      }
      for (const seg of bridges) {
        const a = seg[0] || seg.a, b = seg[1] || seg.b; if (!a || !b) continue;
        const vx=b.x-a.x, vy=b.y-a.y; const len=Math.hypot(vx,vy)||1e-6; const ux=vx/len, uy=vy/len; const nx=-uy, ny=ux;
        ctx.strokeStyle = Palette.dark + '60';
        ctx.lineWidth = Math.max(Math.min(outlineW*1.1, 50), 0.6/safeScale);
        const drawBand = (p)=>{
          const c0x = p.x - ux*abutLen*0.5, c0y = p.y - uy*abutLen*0.5;
          const c1x = p.x + ux*abutLen*0.5, c1y = p.y + uy*abutLen*0.5;
          ctx.beginPath(); ctx.moveTo(c0x + nx*deckW*0.5, c0y + ny*deckW*0.5); ctx.lineTo(c1x + nx*deckW*0.5, c1y + ny*deckW*0.5); ctx.stroke();
          ctx.beginPath(); ctx.moveTo(c0x - nx*deckW*0.5, c0y - ny*deckW*0.5); ctx.lineTo(c1x - nx*deckW*0.5, c1y - ny*deckW*0.5); ctx.stroke();
        };
        drawBand(a); drawBand(b);
        ctx.strokeStyle = Palette.dark + '30';
        ctx.lineWidth = Math.max(0.6/safeScale, Math.min(outlineW*0.6, 50));
        const n = Math.max(2, Math.min(500, Math.floor(len / plankSpacing)));
        for (let i=1;i<n;i++){
          const t = i/n; const px = a.x + vx*t, py = a.y + vy*t;
            ctx.beginPath(); ctx.moveTo(px - nx*deckW*0.5, py - ny*deckW*0.5); ctx.lineTo(px + nx*deckW*0.5, py + ny*deckW*0.5); ctx.stroke();
        }
      }
    }
    ctx.restore();
  }
  
  drawPiers(ctx, piers) {
    if (!piers || piers.length === 0) return;
    
    const safeScale = Math.max(1e-3, this.scale || 1);
    
    ctx.save();
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    
    for (const pier of piers) {
      const {start, end, width} = pier;
      if (!start || !end) continue;
      
      const vx = end.x - start.x;
      const vy = end.y - start.y;
      const len = Math.hypot(vx, vy) || 1e-6;
      const ux = vx / len, uy = vy / len;
      const nx = -uy, ny = ux;
      
      const w = Math.min(width / safeScale, 50);
      
      // Wooden pier deck
      ctx.fillStyle = '#8B7355';
      ctx.beginPath();
      ctx.moveTo(start.x - nx * w * 0.5, start.y - ny * w * 0.5);
      ctx.lineTo(end.x - nx * w * 0.5, end.y - ny * w * 0.5);
      ctx.lineTo(end.x + nx * w * 0.5, end.y + ny * w * 0.5);
      ctx.lineTo(start.x + nx * w * 0.5, start.y + ny * w * 0.5);
      ctx.closePath();
      ctx.fill();
      
      // Dark outline
      ctx.strokeStyle = Palette.dark + '80';
      ctx.lineWidth = Math.max(0.4 / safeScale, w * 0.15);
      ctx.beginPath();
      ctx.moveTo(start.x - nx * w * 0.5, start.y - ny * w * 0.5);
      ctx.lineTo(end.x - nx * w * 0.5, end.y - ny * w * 0.5);
      ctx.lineTo(end.x + nx * w * 0.5, end.y + ny * w * 0.5);
      ctx.lineTo(start.x + nx * w * 0.5, start.y + ny * w * 0.5);
      ctx.closePath();
      ctx.stroke();
      
      // Planks
      ctx.strokeStyle = Palette.dark + '30';
      ctx.lineWidth = Math.max(0.3 / safeScale, w * 0.08);
      const plankSpacing = Math.max(1.0 / safeScale, w * 0.6);
      // Prevent division by zero/infinity
      if (plankSpacing > 0 && isFinite(plankSpacing) && len > 0 && isFinite(len)) {
        const numPlanks = Math.floor(len / plankSpacing);
        const safePlanks = Math.min(numPlanks, 50); // Cap at 50 planks max
        for (let i = 1; i < safePlanks; i++) {
          const t = i / safePlanks;
          const px = start.x + vx * t;
          const py = start.y + vy * t;
          ctx.beginPath();
          ctx.moveTo(px - nx * w * 0.5, py - ny * w * 0.5);
          ctx.lineTo(px + nx * w * 0.5, py + ny * w * 0.5);
          ctx.stroke();
        }
      }
    }
    
    ctx.restore();
  }
  
  drawWaterBodies(ctx, waterBodies) {
    ctx.save();
    
    // Unified water colour - all water uses same colour for seamless blending
    const waterColour = '#A8D5E2';
    
    // Draw all water bodies with FILL ONLY (no strokes) for seamless blending
    for (let wi = 0; wi < waterBodies.length; wi++) {
      const water = waterBodies[wi];
      if (!water || water.length < 3) continue;
      
      // Use same colour for ALL water types (coast, river, canal, pond) for consistent appearance
      ctx.fillStyle = waterColour;
      
      // Draw water polygon with FILL ONLY (no stroke = seamless blending)
      ctx.beginPath();
      ctx.moveTo(water[0].x, water[0].y);
      for (let i = 1; i < water.length; i++) {
        ctx.lineTo(water[i].x, water[i].y);
      }
      ctx.closePath();
      ctx.fill();
      // NO stroke() call = seamless blending where water bodies meet
    }
    
    ctx.restore();
  }
  
  calculateArea(polygon) {
    let area = 0;
    for (let i = 0; i < polygon.length; i++) {
      const p1 = polygon[i];
      const p2 = polygon[(i + 1) % polygon.length];
      area += (p1.x * p2.y - p2.x * p1.y);
    }
    return Math.abs(area / 2);
  }
  
  getBoundsOf(polygon) {
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const p of polygon) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x);
      maxY = Math.max(maxY, p.y);
    }
    return { minX, minY, maxX, maxY };
  }
  
  getPolygonCenter(polygon) {
    let cx = 0, cy = 0;
    for (const p of polygon) {
      cx += p.x;
      cy += p.y;
    }
    return new Point(cx / polygon.length, cy / polygon.length);
  }
  
  getPolygonRadius(polygon) {
    const center = this.getPolygonCenter(polygon);
    let maxDist = 0;
    for (const p of polygon) {
      const dist = Point.distance(p, center);
      if (dist > maxDist) maxDist = dist;
    }
    return maxDist;
  }

  drawLabel(ctx, patch, labelText) {
    if (!labelText) return;
    
    // Calculate centre of patch
    let cx = 0, cy = 0;
    for (const p of patch.shape) {
      cx += p.x;
      cy += p.y;
    }
    cx /= patch.shape.length;
    cy /= patch.shape.length;
    
    ctx.save();
    const fontSize = 10 / this.scale; // Bigger font
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

  drawDistrictLabel(ctx, district) {
    if (!district || !district.name || !district.patches || district.patches.length === 0) return;
    
    // Get the boundary of the district (union of all patches)
    const allPoints = [];
    for (const patch of district.patches) {
      allPoints.push(...patch.shape);
    }
    
    // Find the ridge/equator line through the district
    const ridge = this.getDistrictRidge(allPoints);
    if (!ridge || ridge.length < 2) return;
    
    // Draw curved text along the ridge
    this.drawCurvedText(ctx, district.name, ridge);
  }

  getDistrictRidge(points) {
    if (points.length === 0) return null;
    // PCA-based ridge fitting for stable, gentle curvature
    // 1. Compute centroid
    let sumX = 0, sumY = 0;
    for (const p of points) { sumX += p.x; sumY += p.y; }
    const cx = sumX / points.length;
    const cy = sumY / points.length;

    // 2. Compute covariance components
    let covXX = 0, covYY = 0, covXY = 0;
    for (const p of points) {
      const dx = p.x - cx;
      const dy = p.y - cy;
      covXX += dx * dx;
      covYY += dy * dy;
      covXY += dx * dy;
    }
    covXX /= points.length;
    covYY /= points.length;
    covXY /= points.length;

    // 3. Eigen decomposition for 2x2 covariance
    const trace = covXX + covYY;
    const det = covXX * covYY - covXY * covXY;
    const temp = Math.sqrt(Math.max(0, trace * trace - 4 * det));
    const lambda1 = (trace + temp) / 2; // largest eigenvalue
    // const lambda2 = (trace - temp) / 2; // smaller (unused directly)

    // Eigenvector for lambda1: (covXY, lambda1 - covXX) unless degenerate
    let vx = covXY;
    let vy = lambda1 - covXX;
    if (Math.abs(vx) + Math.abs(vy) < 1e-6) { vx = 1; vy = 0; }
    const len = Math.sqrt(vx * vx + vy * vy);
    vx /= len; vy /= len;

    // Secondary axis (perpendicular)
    const wx = -vy;
    const wy = vx;

    // 4. Project points onto primary axis to get range
    let minT = Infinity, maxT = -Infinity;
    const projected = [];
    for (const p of points) {
      const dx = p.x - cx;
      const dy = p.y - cy;
      const t = dx * vx + dy * vy; // primary coord
      const u = dx * wx + dy * wy; // secondary coord
      projected.push({ t, u });
      if (t < minT) minT = t;
      if (t > maxT) maxT = t;
    }

    const axisLength = maxT - minT;
    if (axisLength < 1e-3) return null;

    // 5. Sample along primary axis and compute average secondary displacement
    const samples = 24;
    const windowSize = axisLength * 0.15;
    const ridge = [];
    for (let i = 0; i <= samples; i++) {
      const tNorm = i / samples;
      const tVal = minT + axisLength * tNorm;
      let sumU = 0, countU = 0;
      for (const pr of projected) {
        if (Math.abs(pr.t - tVal) <= windowSize) { sumU += pr.u; countU++; }
      }
      let avgU = countU > 0 ? (sumU / countU) : 0;
      // Limit curvature amplitude for legibility
      const maxCurve = axisLength * 0.08;
      avgU = Math.max(-maxCurve, Math.min(maxCurve, avgU));
      // Reconstruct point in world space
      const x = cx + vx * tVal + wx * avgU;
      const y = cy + vy * tVal + wy * avgU;
      ridge.push(new Point(x, y));
    }

    // 6. Smooth ridge (simple moving average)
    const smooth = [];
    const smoothRadius = 2;
    for (let i = 0; i < ridge.length; i++) {
      let sx = 0, sy = 0, sc = 0;
      for (let k = -smoothRadius; k <= smoothRadius; k++) {
        const idx = i + k;
        if (idx >= 0 && idx < ridge.length) { sx += ridge[idx].x; sy += ridge[idx].y; sc++; }
      }
      smooth.push(new Point(sx / sc, sy / sc));
    }

    return smooth;
  }

  drawCurvedText(ctx, text, ridge) {
    if (!text || ridge.length < 2) return;
    
    ctx.save();
    // Adaptive font sizing based on ridge extents
    let minX = Infinity, maxX = -Infinity;
    for (const p of ridge) { minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x); }
    const ridgeWidth = maxX - minX;
    const fontSize = Math.max(20, Math.min(40, ridgeWidth * 0.12)) / this.scale;
    ctx.font = `bold ${fontSize}px serif`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';

    // Work on a local path we can reverse for upright text
    let path = ridge.slice();

    // Helper: compute path length
    const getPathLength = (p) => {
      let L = 0;
      for (let i = 0; i < p.length - 1; i++) {
        const dx = p[i + 1].x - p[i].x;
        const dy = p[i + 1].y - p[i].y;
        L += Math.sqrt(dx * dx + dy * dy);
      }
      return L;
    };

    // Helper to get point at distance along current path
    const getPointAtOn = (p, dist) => {
      let remaining = dist;
      for (let i = 0; i < p.length - 1; i++) {
        const dx = p[i + 1].x - p[i].x;
        const dy = p[i + 1].y - p[i].y;
        const segLen = Math.sqrt(dx * dx + dy * dy);
        if (remaining <= segLen) {
          const t = Math.max(0, Math.min(1, remaining / segLen));
          return { x: p[i].x + dx * t, y: p[i].y + dy * t, angle: Math.atan2(dy, dx) };
        }
        remaining -= segLen;
      }
      const last = p[p.length - 1];
      const prev = p[p.length - 2];
      return { x: last.x, y: last.y, angle: Math.atan2(last.y - prev.y, last.x - prev.x) };
    };

    // Determine if text would be upside down at the center; if so, flip path
    const totalLengthForCheck = getPathLength(path);
    const midPosCheck = getPointAtOn(path, totalLengthForCheck / 2);
    const ang = midPosCheck.angle;
    // Canvas y axis is down; treat angles with cos < 0 (pointing left) as upside-down text
    if (Math.cos(ang) < 0) {
      path.reverse();
    }

    // Compute final path length after possible reversal
    const pathLength = getPathLength(path);

    // Helper bound to current path
    const getPointAt = (dist) => getPointAtOn(path, dist);

    // Measure per-character widths
    const charWidths = [];
    let totalCharWidth = 0;
    for (let i = 0; i < text.length; i++) {
      const w = ctx.measureText(text[i]).width;
      charWidths.push(w);
      totalCharWidth += w;
    }
    const letterSpacing = fontSize * 0.1; // small spacing
    const totalWidth = totalCharWidth + letterSpacing * Math.max(0, text.length - 1);

    // If path is too short, use straight text with collision avoidance
    if (pathLength < totalWidth * 0.75) {
      const midIdx = Math.floor(path.length / 2);
      let mid = path[midIdx];
      
      // Create bbox for straight text
      const textWidth = ctx.measureText(text).width;
      const padding = fontSize * 0.25;
      const halfW = textWidth / 2 + padding;
      const halfH = fontSize * 0.6 + padding;
      
      // Try multiple positions to avoid collisions
      const positions = [
        { x: mid.x, y: mid.y, offset: 0 },
        { x: mid.x, y: mid.y + fontSize * 1.5, offset: fontSize * 1.5 },
        { x: mid.x, y: mid.y - fontSize * 1.5, offset: -fontSize * 1.5 },
        { x: mid.x + fontSize, y: mid.y, offset: 0 },
        { x: mid.x - fontSize, y: mid.y, offset: 0 }
      ];
      
      const overlaps = (a, b) => !(a.x + a.w < b.x || b.x + b.w < a.x || a.y + a.h < b.y || b.y + b.h < a.y);
      let foundPosition = null;
      
      for (const pos of positions) {
        const bbox = { x: pos.x - halfW, y: pos.y - halfH, w: halfW * 2, h: halfH * 2 };
        let hasCollision = false;
        
        if (this.labelBBoxes && this.labelBBoxes.length > 0) {
          for (const g of this.labelBBoxes) {
            if (overlaps(bbox, g)) {
              hasCollision = true;
              break;
            }
          }
        }
        
        if (!hasCollision) {
          foundPosition = { pos, bbox };
          break;
        }
      }
      
      // If no position found without collision, try scaling down
      if (!foundPosition) {
        const scaledFontSize = fontSize * 0.7;
        ctx.font = `bold ${scaledFontSize}px serif`;
        const scaledTextWidth = ctx.measureText(text).width;
        const scaledPadding = scaledFontSize * 0.25;
        const scaledHalfW = scaledTextWidth / 2 + scaledPadding;
        const scaledHalfH = scaledFontSize * 0.6 + scaledPadding;
        
        for (const pos of positions) {
          const bbox = { x: pos.x - scaledHalfW, y: pos.y - scaledHalfH, w: scaledHalfW * 2, h: scaledHalfH * 2 };
          let hasCollision = false;
          
          if (this.labelBBoxes && this.labelBBoxes.length > 0) {
            for (const g of this.labelBBoxes) {
              if (overlaps(bbox, g)) {
                hasCollision = true;
                break;
              }
            }
          }
          
          if (!hasCollision) {
            foundPosition = { pos, bbox };
            break;
          }
        }
      }
      
      // If still no position, skip this label
      if (!foundPosition) {
        ctx.restore();
        return;
      }
      
      // Draw the label at the found position
      ctx.strokeStyle = '#FFFFFF';
      ctx.lineWidth = 5 / this.scale;
      ctx.strokeText(text, foundPosition.pos.x, foundPosition.pos.y);
      ctx.fillStyle = '#8B4513';
      ctx.fillText(text, foundPosition.pos.x, foundPosition.pos.y);
      
      if (this.labelBBoxes) this.labelBBoxes.push(foundPosition.bbox);
      ctx.restore();
      return;
    }

    // First pass: compute placements and AABBs; check collisions against existing labels only
    const startOffset = (pathLength - totalWidth) / 2;
    let d = startOffset;
    const placements = [];
    const currentBBoxes = [];
    const padding = fontSize * 0.25; // Add padding to prevent visual overlap
    for (let i = 0; i < text.length; i++) {
      const pos = getPointAt(d + charWidths[i] / 2);
      placements.push(pos);
      const halfW = Math.max(charWidths[i] / 2, fontSize * 0.3) + padding;
      const halfH = fontSize * 0.6 + padding;
      const bbox = { x: pos.x - halfW, y: pos.y - halfH, w: halfW * 2, h: halfH * 2 };
      currentBBoxes.push(bbox);
      d += charWidths[i] + letterSpacing;
    }

    const overlaps = (a, b) => !(a.x + a.w < b.x || b.x + b.w < a.x || a.y + a.h < b.y || b.y + b.h < a.y);
    if (this.labelBBoxes && this.labelBBoxes.length > 0) {
      for (const b of currentBBoxes) {
        for (const g of this.labelBBoxes) {
          if (overlaps(b, g)) { ctx.restore(); return; }
        }
      }
    }

    // Second pass: draw all characters, then register bboxes
    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      const pos = placements[i];
      ctx.save();
      ctx.translate(pos.x, pos.y);
      ctx.rotate(pos.angle);
      ctx.strokeStyle = '#FFFFFF';
      ctx.lineWidth = 3.5 / this.scale;
      ctx.lineJoin = 'round';
      ctx.strokeText(char, 0, 0);
      ctx.fillStyle = '#5A3312';
      ctx.fillText(char, 0, 0);
      ctx.restore();
    }

    if (this.labelBBoxes) this.labelBBoxes.push(...currentBBoxes);
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

  getWardColour3D(wardType) {
    const colours = {
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
    return colours[wardType] || '#A89878';
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
          color: this.getWardColour3D(wardType),
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
    
    // Apply pan offset from 2D view (inverted to match 2D camera behaviour)
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

      for (let i = 0; i < visibleBuildings.length; i++) {
        const building = visibleBuildings[i];
        
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
      
      // Shade colour (or use yellow if hovered)
      let shadedColour;
      if (isHovered) {
        shadedColour = '#FFFF00'; // Bright yellow for hovered building
      } else {
        const hex = tri.color.replace('#', '');
        let r = parseInt(hex.substr(0, 2), 16);
        let g = parseInt(hex.substr(2, 2), 16);
        let b = parseInt(hex.substr(4, 2), 16);
        r = Math.floor(r * tri.brightness);
        g = Math.floor(g * tri.brightness);
        b = Math.floor(b * tri.brightness);
        shadedColour = '#' + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1);
      }
      
      ctx.fillStyle = shadedColour;
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
   * @param {string} roofColour - Colour for roofs
   * @param {string} outlineColour - Colour for outlines
   * @param {number} raised - Height factor for 3D effect (default 0.5)
   * @param {number} scale - Rendering scale
   * @param {string} wardColourTint - Optional ward colour for subtle tinting (hex colour)
   */
  static paint(ctx, buildings, roofColour, outlineColour, raised = 0.5, scale = 1, wardColourTint = null) {
    const strokeWidth = 0.5 / scale;
    let wallOffset = 0;

    // Blend base roof colour with ward tint if provided (25% tint for better visibility)
    let baseRoofColour = roofColour;
    if (wardColourTint) {
      baseRoofColour = this.blendColours(roofColour, wardColourTint, 0.25);
    }
    
    // Draw 3D walls if raised
    if (raised > 0) {
      wallOffset = -1.2 * raised;
      const wallColour = Palette.dark;
      
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
            this.drawWallSegment(ctx, wallSegment, wallOffset, wallColour, outlineColour, strokeWidth);
            wallSegment = null;
          }
        }
        
        // Draw final segment if exists
        if (wallSegment) {
          this.drawWallSegment(ctx, wallSegment, wallOffset, wallColour, outlineColour, strokeWidth);
        }
      }
    }
    
    // Draw roofs with slight colour variation
    for (const building of buildings) {
      // Add slight random variation to roof colour
      const weathering = 0.1;
      const variance = (Random.float() + Random.float() + Random.float()) / 3 * 2 - 1;
      const variedRoof = this.scaleColour(baseRoofColour, Math.pow(2, variance * weathering));
      
      ctx.fillStyle = variedRoof;
      ctx.strokeStyle = outlineColour;
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
      this.drawRoofDetails(ctx, building, wallOffset, strokeWidth, outlineColour);
    }
  }
  
  static drawWallSegment(ctx, segment, offset, wallColour, outlineColour, strokeWidth) {
    // Create bottom edge of wall
    const bottom = segment.map(p => new Point(p.x, p.y - offset));
    bottom.reverse();
    
    // Draw wall face
    ctx.fillStyle = wallColour;
    ctx.strokeStyle = outlineColour;
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
    
    // Draw vertical edges if wall colour differs from outline
    if (wallColour !== outlineColour) {
      ctx.strokeStyle = outlineColour;
      for (let i = 1; i < segment.length - 1; i++) {
        const p = segment[i];
        ctx.beginPath();
        ctx.moveTo(p.x, p.y);
        ctx.lineTo(p.x, p.y - offset);
        ctx.stroke();
      }
    }
  }
  
  static drawRoofDetails(ctx, building, offset, strokeWidth, colour) {
    // Simplified roof detail - just draw towards centre
    const center = {x: 0, y: 0};
    for (const p of building) {
      center.x += p.x;
      center.y += p.y;
    }
    center.x /= building.length;
    center.y /= building.length;
    
    ctx.strokeStyle = colour;
    ctx.lineWidth = strokeWidth;
    
    // Draw lines from edges towards centre for some edges
    for (let i = 0; i < building.length; i++) {
      if (Random.chance(0.3)) { // Only some edges
        const p = building[i];
        const dx = center.x - p.x;
        const dy = center.y - p.y;
        const len = Math.sqrt(dx * dx + dy * dy);
        
        if (len > 2) { // Only if not too close to centre
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
  
  static blendColours(colour1, colour2, ratio) {
    // Parse first colour
    const hex1 = colour1.replace('#', '');
    const r1 = parseInt(hex1.substr(0, 2), 16);
    const g1 = parseInt(hex1.substr(2, 2), 16);
    const b1 = parseInt(hex1.substr(4, 2), 16);
    
    // Parse second colour
    const hex2 = colour2.replace('#', '');
    const r2 = parseInt(hex2.substr(0, 2), 16);
    const g2 = parseInt(hex2.substr(2, 2), 16);
    const b2 = parseInt(hex2.substr(4, 2), 16);
    
    // Blend
    const r = Math.floor(r1 * (1 - ratio) + r2 * ratio);
    const g = Math.floor(g1 * (1 - ratio) + g2 * ratio);
    const b = Math.floor(b1 * (1 - ratio) + b2 * ratio);
    
    return '#' + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1);
  }

  static scaleColour(colourHex, factor) {
    // Parse hex colour
    const hex = colourHex.replace('#', '');
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
    const fieldColour = '#C9B896';  // Definite tan/brown for farm fields
    const darkColour = Palette.dark;
    
    // Draw field plots
    ctx.fillStyle = fieldColour;
    ctx.strokeStyle = darkColour;
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
      ctx.strokeStyle = darkColour;
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
      BuildingPainter.paint(ctx, farm.buildings, Palette.roof, darkColour, 0.3, scale);
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
// View Architecture 
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
 * Handles fill colours, patterns, and details for each ward type
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
    
    // Use inset shape if available (respects walls/water), otherwise use full patch shape
    const shapeToRender = (patch.availableShape && patch.availableShape.length >= 3)
      ? patch.availableShape
      : patch.shape;
    
    // If we have a wall polygon, clip INSIDE for inside wards and OUTSIDE for outside wards
    const wall = this.settings.interiorClip;
    let didClip = false;
    if (Array.isArray(wall) && wall.length >= 3) {
      didClip = true;
      ctx.save();
      ctx.beginPath();
      // Use withinCity flag consistently
      if (patch.withinCity) {
        // Interior clip
        ctx.moveTo(wall[0].x, wall[0].y);
        for (let i = 1; i < wall.length; i++) ctx.lineTo(wall[i].x, wall[i].y);
        ctx.closePath();
        ctx.clip();
      } else {
        // Exterior clip: big rect minus wall (evenodd)
        const M = 1e5; // large extent to cover canvas
        ctx.moveTo(-M, -M);
        ctx.lineTo(M, -M);
        ctx.lineTo(M, M);
        ctx.lineTo(-M, M);
        ctx.closePath();
        ctx.moveTo(wall[0].x, wall[0].y);
        for (let i = 1; i < wall.length; i++) ctx.lineTo(wall[i].x, wall[i].y);
        ctx.closePath();
        if (ctx.clip instanceof Function) {
          try { ctx.clip('evenodd'); } catch { ctx.clip(); }
        } else {
          ctx.clip();
        }
      }
    }

    // Fill the patch: override to terrain tones for outside cells
    let fillColour = patch.color || this.palette.light;
    if (!patch.withinCity) {
      // Compute soft terrain tint based on centroid noise (beige/tan tones)
      let cx = 0, cy = 0; for (const p of shapeToRender) { cx += p.x; cy += p.y; } cx /= shapeToRender.length; cy /= shapeToRender.length;
      const n = (PerlinNoise.noise(cx * 0.05, cy * 0.05) + 1) * 0.5;
      const h = 40 * (1 - n) + 45 * n;  // Beige/tan hue range (40-45 degrees)
      const s = 25 * (1 - n) + 30 * n;  // Lower saturation for beige
      const l = 80 * (1 - n) + 85 * n;  // Light tones
      fillColour = `hsl(${h.toFixed(0)}, ${s.toFixed(0)}%, ${l.toFixed(0)}%)`;
    }
    ctx.fillStyle = fillColour;
    ctx.strokeStyle = this.palette.dark;
    ctx.lineWidth = showCellOutlines ? 0.5 : 0;
    
    ctx.beginPath();
    ctx.moveTo(shapeToRender[0].x, shapeToRender[0].y);
    for (let i = 1; i < shapeToRender.length; i++) {
      ctx.lineTo(shapeToRender[i].x, shapeToRender[i].y);
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
      
      BuildingPainter.paint(ctx, processedBuildings, this.palette.roof, this.palette.dark, 0.5, 1, patch.wardColorTint);
    }
    
    // Draw farm details if this is a farm
    if (showFarms && patch.type === 'farm' && patch.furrows) {
      this.drawFarmDetails(ctx, patch);
    }
    
    // Restore after optional clip
    if (didClip) ctx.restore();
    
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
    
    // Draw in three passes: major roads, minor roads, then alleys (nearly invisible)
    if (showMajor) {
      this.drawRoadLayer(ctx, this.roads.filter(r => r.major && !r.isAlley), true, false);
    }
    if (showMinor) {
      this.drawRoadLayer(ctx, this.roads.filter(r => !r.major && !r.isAlley), false, false);
    }
    // Draw alleys last with minimal visibility
    this.drawRoadLayer(ctx, this.roads.filter(r => r.isAlley), false, true);
    
    ctx.restore();
  }
  
  drawRoadLayer(ctx, roads, isMajor, isAlley) {
    const baseWidth = this.settings.streetWidth || 4.0;
    
    if (isAlley) {
      // Alleys: nearly invisible (3% opacity, extremely thin)
      ctx.strokeStyle = this.palette.dark + '08'; // 3% opacity
      ctx.lineWidth = baseWidth * 0.03;
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      
      for (const road of roads) {
        this.drawRoad(ctx, road);
      }
    } else {
      // Regular roads: normal two-pass rendering
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
  }
  
  draw(ctx, options = {}) {
    if (this.walls.length === 0) return;
    
    const showTowers = options.showTowers !== false;
    const showGates = options.showGates !== false;
    
    ctx.save();
    
    // Separate city walls from citadel walls
    const cityWalls = this.walls.filter(w => !w.isCitadel);
    const citadelWalls = this.walls.filter(w => w.isCitadel);
    
    // Clip to OUTSIDE castle areas before drawing city walls
    if (citadelWalls.length > 0) {
      ctx.save();
      const M = 1e5;
      ctx.beginPath();
      // Big outer rect
      ctx.moveTo(-M, -M);
      ctx.lineTo(M, -M);
      ctx.lineTo(M, M);
      ctx.lineTo(-M, M);
      ctx.closePath();
      // Subtract each castle area
      for (const citadel of citadelWalls) {
        if (citadel.path && citadel.path.length > 0) {
          ctx.moveTo(citadel.path[0].x, citadel.path[0].y);
          for (let i = 1; i < citadel.path.length; i++) {
            ctx.lineTo(citadel.path[i].x, citadel.path[i].y);
          }
          ctx.closePath();
        }
      }
      try { ctx.clip('evenodd'); } catch { ctx.clip(); }
    }
    
    // Draw city wall segments (now clipped to outside castles)
    ctx.strokeStyle = this.palette.dark;
    ctx.lineWidth = this.settings.wallThickness || 5;
    ctx.lineCap = 'square';
    ctx.lineJoin = 'miter';
    
    for (const wall of cityWalls) {
      this.drawWallSegment(ctx, wall);
    }
    
    if (citadelWalls.length > 0) {
      ctx.restore();
    }
    
    // Draw citadel walls (reset stroke properties after restore)
    ctx.strokeStyle = this.palette.dark;
    ctx.lineWidth = this.settings.wallThickness || 5;
    ctx.lineCap = 'square';
    ctx.lineJoin = 'miter';
    
    for (const wall of citadelWalls) {
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
    
    const wallThickness = this.settings.wallThickness || 5;
    
    ctx.beginPath();
    ctx.moveTo(wall.path[0].x, wall.path[0].y);
    for (let i = 1; i < wall.path.length; i++) {
      ctx.lineTo(wall.path[i].x, wall.path[i].y);
    }
    // Only close path for non-citadel walls
    if (!wall.isCitadel) {
      ctx.closePath();
    }
    ctx.stroke();
    
    // Erase gaps at gates
    if (wall.gates && wall.gates.length > 0) {
      ctx.save();
      ctx.globalCompositeOperation = 'destination-out';
      ctx.strokeStyle = 'black';
      ctx.lineWidth = wallThickness * 2;
      ctx.lineCap = 'round';
      
      for (const gate of wall.gates) {
        ctx.beginPath();
        ctx.arc(gate.x, gate.y, wallThickness * 1.5, 0, Math.PI * 2);
        ctx.fill();
      }
      
      ctx.restore();
    }
  }
  
  drawTower(ctx, tower) {
    // Compute tower radius dynamically from wall thickness
    const wallThickness = this.settings.wallThickness || 5;
    const radius = tower.radius || (wallThickness * 0.8);
    
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
    // Scale gate size with wall thickness
    const wallThickness = this.settings.wallThickness || 5;
    const width = gate.width || (wallThickness * 1.6);
    const height = gate.height || (wallThickness * 2.4);
    
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

    // Draw district names with curved text
    if (StateManager.showRegionNames && this.model.districts) {
      for (const district of this.model.districts) {
        this.renderer.drawDistrictLabel(ctx, district);
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
// District Name Generator
// ============================================================================

class DistrictNameGenerator {
  static prefixes = ['North', 'South', 'East', 'West', 'Old', 'New', 'High', 'Low', 'Upper', 'Lower', 'Little', 'Great'];
  static types = ['Quarter', 'District', 'Town', 'End', 'Side', 'Gate', 'Cross', 'Market', 'Square'];
  static suffixes = ['Borough', 'Village', 'Heights', 'Fields', 'Green', 'Vale', 'Hill', 'Bridge', 'Crossing'];
  static adjectives = ['Royal', 'Common', 'Merchant', 'Craft', 'Temple', 'Mill', 'Garden', 'River', 'Stone', 'Iron'];
  
  static pick(arr) {
    return arr[Random.int(0, arr.length)];
  }
  
  static generate() {
    const roll = Random.float();
    
    if (roll < 0.3) {
      // Prefix + Type ("North Quarter")
      return this.pick(this.prefixes) + ' ' + this.pick(this.types);
    } else if (roll < 0.6) {
      // Adjective + Type ("Merchant Ward")
      return this.pick(this.adjectives) + ' ' + this.pick(this.types);
    } else if (roll < 0.8) {
      // Prefix + Adjective + Type ("Old Craft Quarter")
      return this.pick(this.prefixes) + ' ' + this.pick(this.adjectives) + ' ' + this.pick(this.types);
    } else {
      // Adjective + Suffix ("Royal Borough")
      return this.pick(this.adjectives) + ' ' + this.pick(this.suffixes);
    }
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
  static urbanCastle = false; // Castle inside the city walls
  static wallsNeeded = true;
  static gatesNeeded = true;
  static gridChaos = 0.7;
  static sizeChaos = 0.8;
  static cellChaos = 1.0;
  static alleyWidth = 2.4;
  static streetWidth = 3.5;
  static buildingGap = 0.2;
  static showLabels = false;
  static wallThickness = 2.0;
  static showCellOutlines = false;
  static showBuildings = true;
  static showStreets = true;
  static showWater = true; // Show water bodies (coast/river) - default enabled
  static coast = 1;         // 1 to force coast, 0 to disable
  static river = 1;         // 1 to enable river (independent)
  static canal = 0;         // 1 to enable canal (independent)
  static riverType = 'none'; // back-compat: 'none' | 'river' | 'canal' | 'both'
  static riverMeander = 0.5; // 0-1: micro-meander noise intensity (0=pure sine, 1=max chaos)
  static lotsMode = 'normal';  // Building style: 'lots', 'normal', or 'mix'
  static plazaChance = 0.05; // Chance of central feature in plaza
  static useViewArchitecture = false; // Toggle for view-based rendering
  static flythroughActive = false; // Flythrough camera mode
  static showTrees = true; // Trees default enabled per user prefs
  static shantytown = true; // Shantytown default enabled per user prefs
  static cameraOffsetX = 0; // Camera pan X offset
  static cameraOffsetY = 0; // Camera pan Y offset
  static zoom = 1.0; // Zoom level for 2D rendering
  static view3D = false;     // Toggle between 2D and 3D rendering
  static camera3DHeight = 80; // 3D camera height for overview
  static camera3DFOV = 60;   // 3D camera field of view (degrees)
  static camera3DAngle = 0;  // 3D camera rotation angle (radians)
  static camera3DNear = 0.1; // 3D camera near clipping plane
  static camera3DFar = 4000; // 3D camera far clipping plane
  static buildingCount = 1000; // Number of buildings to render (1-1000)
  static showRegionNames = true; // Display region/district names over grouped wards

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

    const bool = (v) => v === '1' || v === 'true' || v === 'yes';
    if (params.has('citadel')) StateManager.citadelNeeded = bool(params.get('citadel'));
    if (params.has('urban_castle')) StateManager.urbanCastle = bool(params.get('urban_castle'));
    if (params.has('plaza')) StateManager.plazaNeeded = bool(params.get('plaza'));
    if (params.has('temple')) {
      // temple simply increases chance of cathedral-like ward
      StateManager.templeBoost = bool(params.get('temple')) ? 1 : 0;
    }
    if (params.has('walls')) StateManager.wallsNeeded = bool(params.get('walls'));
    if (params.has('gates')) StateManager.gatesNeeded = bool(params.get('gates'));
    if (params.has('coast')) StateManager.coast = bool(params.get('coast')) ? 1 : 0;
    if (params.has('river')) StateManager.river = bool(params.get('river')) ? 1 : 0;
    if (params.has('canal')) StateManager.canal = bool(params.get('canal')) ? 1 : 0;
    if (params.has('riverType')) {
      const rt = params.get('riverType');
      if (rt === 'river' || rt === 'canal' || rt === 'none' || rt === 'both') StateManager.riverType = rt;
    }
    // Auto-determine riverType from individual flags
    if (StateManager.river === 1 && StateManager.canal === 1) {
      StateManager.riverType = 'both';
    } else if (StateManager.river === 1) {
      StateManager.riverType = 'river';
    } else if (StateManager.canal === 1) {
      StateManager.riverType = 'canal';
    } else {
      StateManager.riverType = 'none';
    }
    // Explicit water toggle param support
    if (params.has('water')) StateManager.showWater = bool(params.get('water'));
    // If URL forces any water, auto-enable Show Water
    if ((StateManager.coast === 1 || StateManager.river === 1 || StateManager.canal === 1) && !params.has('water')) {
      StateManager.showWater = true;
    }
    if (params.has('greens')) StateManager.showTrees = bool(params.get('greens'));
    if (params.has('shantytown')) StateManager.shantytown = bool(params.get('shantytown'));
    if (params.has('lots')) StateManager.lotsMode = bool(params.get('lots'));
    if (params.has('regions')) StateManager.showRegionNames = bool(params.get('regions'));
    const display = params.get('display');
    if (display && display.toLowerCase() === 'lots') StateManager.lotsMode = 'lots';
    if (display && display.toLowerCase() === 'normal') StateManager.lotsMode = 'normal';
    if (display && display.toLowerCase() === 'mix') StateManager.lotsMode = 'mix';
  }

  static pushParams() {
    if (StateManager.seed === -1) {
      Random.reset();
      StateManager.seed = Random.seed;
    }
    
    const url = new URL(window.location.href);
    url.searchParams.set('size', StateManager.size);
    url.searchParams.set('seed', StateManager.seed);
    url.searchParams.set('citadel', StateManager.citadelNeeded ? 1 : 0);
    url.searchParams.set('urban_castle', StateManager.urbanCastle ? 1 : 0);
    url.searchParams.set('plaza', StateManager.plazaNeeded ? 1 : 0);
    url.searchParams.set('walls', StateManager.wallsNeeded ? 1 : 0);
    url.searchParams.set('gates', StateManager.gatesNeeded ? 1 : 0);
    url.searchParams.set('coast', StateManager.coast ? 1 : 0);
    url.searchParams.set('river', StateManager.river ? 1 : 0);
    url.searchParams.set('canal', StateManager.canal ? 1 : 0);
    url.searchParams.set('riverType', StateManager.riverType);
    url.searchParams.set('water', StateManager.showWater ? 1 : 0);
    url.searchParams.set('greens', StateManager.showTrees ? 1 : 0);
    url.searchParams.set('shantytown', StateManager.shantytown ? 1 : 0);
    url.searchParams.set('lots', StateManager.lotsMode ? 1 : 0);
    url.searchParams.set('regions', StateManager.showRegionNames ? 1 : 0);
    
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
    
    // Ensure URL params are respected at startup
    if (typeof StateManager.pullParams === 'function') {
      StateManager.pullParams();
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
    this.flythroughCamera = new FlythroughCamera(this.model, this.renderer);
    // Clear cached trees when regenerating
    this.renderer.globalTrees = null;
    this.renderer.render();
    
    console.log('City generated:', { seed: StateManager.seed, size: StateManager.size });
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
      console.log('Flythrough start');
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
      // Debug (suppressed): restarting stopped flythrough camera
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
