#![allow(clippy::identity_op)]
#![allow(clippy::erasing_op)]

use std::{cmp::{min_by_key, Ordering}, collections::BTreeMap};

type Point = (f32, f32);

/// returns Greater if c is on the left side of the line a -> b,
/// or Equal if is on the line, or Less if is on the right side.
fn ori(a: &Point, b: &Point, c: &Point) -> Ordering {
    let ca = (a.0 - c.0, a.1 - c.1);
    let cb = (b.0 - c.0, b.1 - c.1);

    // deal with infinite points
    let ca = if ca.0.is_infinite() { (ca.0.signum(), ca.1.signum()) } else { ca };
    let cb = if cb.0.is_infinite() { (cb.0.signum(), cb.1.signum()) } else { cb };

    (ca.0 * cb.1 - ca.1 * cb.0).partial_cmp(&0.0).unwrap()
}

#[repr(usize)]
enum Triside {
    Outside0 = 0,
    Outside1 = 1,
    Outside2 = 2,
    Inside = 3,
}

/// returns 3 if p is inside the triangle or on the edge,
/// or 0, 1, 2 if p is outside this side of the triangle.
fn triside(a: &Point, b: &Point, c: &Point, p: &Point) -> Triside {
    if ori(b, c, p).is_lt() {
        return Triside::Outside0;
    }
    if ori(c, a, p).is_lt() {
        return Triside::Outside1;
    }
    if ori(a, b, p).is_lt() {
        return Triside::Outside2;
    }
    Triside::Inside
}

/// returns Greater if d is in the circumcircle of a, b, c,
/// or Equal if is on the circle, or Less if is outside the circle.
fn incirc(a: &Point, b: &Point, c: &Point, d: &Point) -> Ordering {
    let da = (a.0 - d.0, a.1 - d.1);
    let db = (b.0 - d.0, b.1 - d.1);
    let dc = (c.0 - d.0, c.1 - d.1);
    let da2 = da.0 * da.0 + da.1 * da.1;
    let db2 = db.0 * db.0 + db.1 * db.1;
    let dc2 = dc.0 * dc.0 + dc.1 * dc.1;

    // deal with infinite points
    let da = if da.0.is_infinite() { (da.0.signum(), da.1.signum()) } else { da };
    let db = if db.0.is_infinite() { (db.0.signum(), db.1.signum()) } else { db };
    let dc = if dc.0.is_infinite() { (dc.0.signum(), dc.1.signum()) } else { dc };
    let (da2, db2, dc2) = if da2.is_infinite() || db2.is_infinite() || dc2.is_infinite() {
        (
            if da2.is_infinite() { 1.0 } else { 0.0 },
            if db2.is_infinite() { 1.0 } else { 0.0 },
            if dc2.is_infinite() { 1.0 } else { 0.0 },
        )
    } else {
        (da2, db2, dc2)
    };

    let m = [
        [da.0, da.1, da2],
        [db.0, db.1, db2],
        [dc.0, dc.1, dc2],
    ];
    let det =
        m[0][0] * m[1][1] * m[2][2]
        + m[0][1] * m[1][2] * m[2][0]
        + m[0][2] * m[1][0] * m[2][1]
        - m[0][2] * m[1][1] * m[2][0]
        - m[0][0] * m[1][2] * m[2][1]
        - m[0][1] * m[1][0] * m[2][2];
    det.partial_cmp(&0.0).unwrap()
}

fn hilbert_dist<const R: u32>(x: f32, y: f32) -> u32 {
    let m = 2_u32.pow(R);
    let mut x = ((x * m as f32).floor() as u32).clamp(0, m - 1);
    let mut y = ((y * m as f32).floor() as u32).clamp(0, m - 1);
    let mut result = 0_u32;
    for i in (0..R).rev() {
        let center = 2_u32.pow(i);
        let quad_area = center.pow(2);
        match (x < center, y < center) {
            (true, true) => {
                (x, y) = (y, x);
            }
            (true, false) => {
                result += quad_area;
                (x, y) = (x, y - center);
            }
            (false, false) => {
                result += quad_area * 2;
                (x, y) = (x - center, y - center);
            }
            (false, true) => {
                result += quad_area * 3;
                (x, y) = (center - 1 - y, center - 1 - (x - center));
            }
        }
    }
    result
}

// corner points
// const CORNER1: Point = (-1e5, -1e5);
// const CORNER2: Point = ( 1e5, -1e5);
// const CORNER3: Point = ( 1e5,  1e5);
// const CORNER4: Point = (-1e5,  1e5);
const CORNER1: Point = (-f32::INFINITY, -f32::INFINITY);
const CORNER2: Point = ( f32::INFINITY, -f32::INFINITY);
const CORNER3: Point = ( f32::INFINITY,  f32::INFINITY);
const CORNER4: Point = (-f32::INFINITY,  f32::INFINITY);

const MIN_WIDTH: f32 = 1e-5;
const HASH_SIZE: u32 = 8;

pub type VIndex = usize;
pub type EIndex = usize;
pub type FIndex = usize;

struct Delaunay {
    points: Vec<Point>,
    // [a_index, b_index, c_index]
    triangles: Vec<[VIndex; 3]>,
    // [bc_adj, ca_adj, ab_adj],  adj = tri_index * 3 + side or BD for unmovable edge
    adjacencies: Vec<[EIndex; 3]>,
    // (bottom-left point, width)
    bbox: (Point, f32),
    // point_index -> hash
    hashes: Vec<u32>,
    // hash -> tri_index,  each hash indicates a grid region
    grid: BTreeMap<u32, FIndex>,
}

impl Delaunay {
    const BD: EIndex = usize::MAX;

    pub fn new(bbox: (Point, f32), capacity: usize) -> Self {
        let mut res = Self {
            bbox,
            points: Vec::with_capacity(capacity + 4),
            // by Euler characteristic, the maximal number of faces of triangluation of V points is 2V - 6
            // (assume it has rectangle convex hull)
            triangles: Vec::with_capacity(capacity * 2 + 2),
            adjacencies: Vec::with_capacity(capacity * 2),
            hashes: Vec::with_capacity(capacity + 4),
            grid: BTreeMap::new(),
        };

        // add four bounding box points
        res.points.push(CORNER1);
        res.points.push(CORNER2);
        res.points.push(CORNER3);
        res.points.push(CORNER4);

        res.triangles.push([0, 1, 2]);
        res.triangles.push([2, 3, 0]);
        res.adjacencies.push([Self::BD, 1*3+1, Self::BD]);
        res.adjacencies.push([Self::BD, 0*3+1, Self::BD]);

        res.hashes.push(res.hash(&res.points[0]));
        res.hashes.push(res.hash(&res.points[1]));
        res.hashes.push(res.hash(&res.points[2]));
        res.hashes.push(res.hash(&res.points[3]));

        res.grid.insert(res.hashes[0], 0);
        res.grid.insert(res.hashes[1], 0);
        res.grid.insert(res.hashes[2], 1);
        res.grid.insert(res.hashes[3], 1);
        
        res
    }
    
    fn hash(&self, &(x, y): &Point) -> u32 {
        let ((x0, y0), w) = &self.bbox;
        hilbert_dist::<HASH_SIZE>((x - x0) / w, (y - y0) / w)
    }

    // find triangle on this point (Ok), or the triangle contains points[i] (Err)
    pub fn find(&self, p: VIndex) -> Result<FIndex, FIndex> {
        let point = &self.points[p];
        let hash = self.hashes[p];
        // find the nearest triangle in the grid
        let mut t = *min_by_key(
            self.grid.range(hash..).next(),
            self.grid.range(..hash).next_back(),
            |e| e.map(|(h, _)| h.abs_diff(hash)).unwrap_or(u32::MAX),
        ).unwrap().1;
        // walk to the point
        loop {
            let [a, b, c] = self.triangles[t];
            if [a, b, c].contains(&p) { return Ok(t); }
            let side = triside(&self.points[a], &self.points[b], &self.points[c], point);
            if let Triside::Inside = side { break; }
            let edge = self.adjacencies[t][side as usize];
            if edge == Self::BD {
                panic!("invalid");
            }
            t = edge / 3;
        }
        Err(t)
    }

    pub fn flip(&mut self, e: EIndex) {
        let (tri, side) = (e / 3, e % 3);
        let e_ = self.adjacencies[tri][side];
        assert!(e_ != Self::BD);
        let (tri_, side_) = (e_ / 3, e_ % 3);
        
        let a = self.triangles[tri][(side+0)%3];
        let b = self.triangles[tri][(side+1)%3];
        let c = self.triangles[tri_][(side_+0)%3];
        let d = self.triangles[tri_][(side_+1)%3];

        let da = self.adjacencies[tri][(side+1)%3];
        let ab = self.adjacencies[tri][(side+2)%3];
        let bc = self.adjacencies[tri_][(side_+1)%3];
        let cd = self.adjacencies[tri_][(side_+2)%3];

        // flip triangles
        self.triangles[tri][(side+0)%3] = b;
        self.triangles[tri][(side+1)%3] = c;
        self.triangles[tri][(side+2)%3] = a;
        self.triangles[tri_][(side_+0)%3] = d;
        self.triangles[tri_][(side_+1)%3] = a;
        self.triangles[tri_][(side_+2)%3] = c;

        self.adjacencies[tri][(side+1)%3] = ab;
        self.adjacencies[tri][(side+2)%3] = bc;
        self.adjacencies[tri_][(side_+1)%3] = cd;
        self.adjacencies[tri_][(side_+2)%3] = da;

        // fix adjacencies
        if ab != Self::BD { self.adjacencies[ab/3][ab%3] = tri*3+(side+1)%3; }
        if bc != Self::BD { self.adjacencies[bc/3][bc%3] = tri*3+(side+2)%3; }
        if cd != Self::BD { self.adjacencies[cd/3][cd%3] = tri_*3+(side_+1)%3; }
        if da != Self::BD { self.adjacencies[da/3][da%3] = tri_*3+(side_+2)%3; }

        // update grid
        // self.grid.insert(self.hashes[a], tri);
        self.grid.insert(self.hashes[b], tri);
        // self.grid.insert(self.hashes[c], tri_);
        self.grid.insert(self.hashes[d], tri_);
    }

    pub fn add(&mut self, point: &Point) -> VIndex {
        let hash = self.hash(point);
        let p = self.points.len();
        self.points.push(*point);
        self.hashes.push(hash);

        let t = self.find(p).unwrap_err();

        // divide triangle
        let (e1, e2, e3) = {
            let [a, b, c] = self.triangles[t];
            let [bc, ca, ab] = self.adjacencies[t];
            // indices for new triangles
            let t1 = t;
            let t2 = self.triangles.len();
            let t3 = self.triangles.len() + 1;
            // add new triangles
            self.triangles[t] = [p, b, c];
            self.triangles.push([a, p, c]);
            self.triangles.push([a, b, p]);
            // add adjacency for new triangles
            self.adjacencies[t] = [bc, t2*3+0, t3*3+0];
            self.adjacencies.push([t1*3+1, ca, t3*3+1]);
            self.adjacencies.push([t1*3+2, t2*3+2, ab]);
            // modify adjacency for adjacent triangles
            if bc != Self::BD { self.adjacencies[bc/3][bc%3] = t1*3+0; }
            if ca != Self::BD { self.adjacencies[ca/3][ca%3] = t2*3+1; }
            if ab != Self::BD { self.adjacencies[ab/3][ab%3] = t3*3+2; }
            // update grid
            self.grid.insert(hash, t2);
            self.grid.insert(self.hashes[a], t2);
            // self.grid.insert(self.hashes[b], t1);
            // self.grid.insert(self.hashes[c], t1);
            (t1*3+0, t2*3+1, t3*3+2)
        };

        // fix star region
        let mut stack = vec![e1, e2, e3];
        while let Some(e) = stack.pop() {
            let (tri, side) = (e / 3, e % 3);
            let e_ = self.adjacencies[tri][side];
            if e_ == Self::BD { continue; }
            let (tri_, side_) = (e_ / 3, e_ % 3);

            // check if it is delaunay
            let [a, b, c] = self.triangles[tri_];
            if incirc(&self.points[a], &self.points[b], &self.points[c], point) != Ordering::Greater {
                continue;
            }

            // flip triangle
            self.flip(e);

            // add flipped triangles to stack
            stack.push(tri*3+(side+2)%3);
            stack.push(tri_*3+(side_+1)%3);
        }

        p
    }

    pub fn get_triangles(&self) -> Vec<[VIndex; 3]> {
        // remove boundary
        self.triangles.iter()
            .cloned()
            .filter(|&[a, b, c]| a >= 4 && b >= 4 && c >= 4)
            .map(|[a, b, c]| [a - 4, b - 4, c - 4])
            .collect()
    }
}

pub fn delaunay(points: &[Point]) -> Vec<[VIndex; 3]> {
    assert!(points.iter().all(|&(x, y)| x.is_finite() && y.is_finite()));
    let bbox = {
        let x_min = points.iter().map(|p| p.0).reduce(|a, b| a.min(b)).unwrap_or(0.0);
        let y_min = points.iter().map(|p| p.1).reduce(|a, b| a.min(b)).unwrap_or(0.0);
        let x_max = points.iter().map(|p| p.0).reduce(|a, b| a.max(b)).unwrap_or(0.0);
        let y_max = points.iter().map(|p| p.1).reduce(|a, b| a.max(b)).unwrap_or(0.0);
        let width = (x_max - x_min).max(y_max - y_min).max(MIN_WIDTH);
        ((x_min, y_min), width)
    };
    let mut engine = Delaunay::new(bbox, points.len());
    for point in points {
        engine.add(point);
    }
    engine.get_triangles()
}
