#![allow(clippy::identity_op)]
#![allow(clippy::erasing_op)]

use std::{
    cmp::{min_by_key, Ordering},
    collections::{BTreeMap, BTreeSet, HashMap},
};

type Point = (f32, f32);

/// returns Greater if c is on the left side of the line a -> b,
/// or Equal if is on the line, or Less if is on the right side.
fn ori(a: &Point, b: &Point, c: &Point) -> Ordering {
    let ca = (a.0 - c.0, a.1 - c.1);
    let cb = (b.0 - c.0, b.1 - c.1);

    // deal with infinite points
    let ca = if ca.0.is_infinite() {
        (ca.0.signum(), ca.1.signum())
    } else {
        ca
    };
    let cb = if cb.0.is_infinite() {
        (cb.0.signum(), cb.1.signum())
    } else {
        cb
    };

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
    let da = if da.0.is_infinite() {
        (da.0.signum(), da.1.signum())
    } else {
        da
    };
    let db = if db.0.is_infinite() {
        (db.0.signum(), db.1.signum())
    } else {
        db
    };
    let dc = if dc.0.is_infinite() {
        (dc.0.signum(), dc.1.signum())
    } else {
        dc
    };
    let (da2, db2, dc2) = if da2.is_infinite() || db2.is_infinite() || dc2.is_infinite() {
        (
            if da2.is_infinite() { 1.0 } else { 0.0 },
            if db2.is_infinite() { 1.0 } else { 0.0 },
            if dc2.is_infinite() { 1.0 } else { 0.0 },
        )
    } else {
        (da2, db2, dc2)
    };

    let m = [[da.0, da.1, da2], [db.0, db.1, db2], [dc.0, dc.1, dc2]];
    let det =
        m[0][0] * m[1][1] * m[2][2] + m[0][1] * m[1][2] * m[2][0] + m[0][2] * m[1][0] * m[2][1]
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
const CORNER2: Point = (f32::INFINITY, -f32::INFINITY);
const CORNER3: Point = (f32::INFINITY, f32::INFINITY);
const CORNER4: Point = (-f32::INFINITY, f32::INFINITY);

const MIN_WIDTH: f32 = 1e-5;
const HASH_SIZE: u32 = 8;

pub type VIndex = usize;
pub type EIndex = usize;
pub type FIndex = usize;

struct Delaunay {
    points: Vec<Point>,
    // [a_index, b_index, c_index]
    vertices: Vec<[VIndex; 3]>,
    // [bc_adj, ca_adj, ab_adj],  adj = tri_index * 3 + side or BD for unmovable edge
    adjacencies: Vec<[EIndex; 3]>,
    fixed_edges: BTreeSet<EIndex>,
    // (bottom-left point, width)
    bbox: (Point, f32),
    // point_index -> hash
    hashes: Vec<u32>,
    // hash -> tri_index,  each hash indicates a grid region
    grid: BTreeMap<u32, FIndex>,
}

impl Delaunay {
    const BD: EIndex = usize::MAX;

    fn rot(e: EIndex, s: usize) -> EIndex {
        assert!(e != Self::BD);
        assert!([0, 1, 2].contains(&e));
        e / 3 * 3 + (e + s) % 3
    }
    fn vertex(&self, e: EIndex) -> VIndex {
        assert!(e != Self::BD);
        self.vertices[e / 3][e % 3]
    }
    fn adjacent(&self, e: EIndex) -> EIndex {
        assert!(e != Self::BD);
        self.adjacencies[e / 3][e % 3]
    }
    fn vertex_mut(&mut self, e: EIndex) -> &mut VIndex {
        assert!(e != Self::BD);
        &mut self.vertices[e / 3][e % 3]
    }
    fn adjacent_mut(&mut self, e: EIndex) -> &mut EIndex {
        assert!(e != Self::BD);
        &mut self.adjacencies[e / 3][e % 3]
    }

    fn new(bbox: (Point, f32), capacity: usize) -> Self {
        let mut res = Self {
            bbox,
            points: Vec::with_capacity(capacity + 4),
            // by Euler characteristic, the maximal number of faces of triangluation of V points is 2V - 6
            // (assume it has rectangle convex hull)
            vertices: Vec::with_capacity(capacity * 2 + 2),
            fixed_edges: BTreeSet::new(),
            adjacencies: Vec::with_capacity(capacity * 2),
            hashes: Vec::with_capacity(capacity + 4),
            grid: BTreeMap::new(),
        };

        // add four bounding box points
        res.points.push(CORNER1);
        res.points.push(CORNER2);
        res.points.push(CORNER3);
        res.points.push(CORNER4);

        res.vertices.push([0, 1, 2]);
        res.vertices.push([2, 3, 0]);
        res.adjacencies.push([Self::BD, 1 * 3 + 1, Self::BD]);
        res.adjacencies.push([Self::BD, 0 * 3 + 1, Self::BD]);

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
    fn find(&self, p: VIndex) -> Result<FIndex, FIndex> {
        let point = &self.points[p];
        let hash = self.hashes[p];
        // find the nearest triangle in the grid
        let mut t = *min_by_key(
            self.grid.range(hash..).next(),
            self.grid.range(..hash).next_back(),
            |e| e.map(|(h, _)| h.abs_diff(hash)).unwrap_or(u32::MAX),
        )
        .unwrap()
        .1;
        // walk to the point
        loop {
            let [a, b, c] = self.vertices[t];
            if [a, b, c].contains(&p) {
                return Ok(t);
            }
            let side = triside(&self.points[a], &self.points[b], &self.points[c], point);
            if let Triside::Inside = side {
                break;
            }
            let edge = self.adjacencies[t][side as usize];
            if edge == Self::BD {
                panic!("invalid");
            }
            t = edge / 3;
        }
        Err(t)
    }

    fn flip(&mut self, e: EIndex) {
        assert!(e != Self::BD);
        let e_ = self.adjacent(e);
        assert!(e_ != Self::BD);
        assert!(!self.fixed_edges.contains(&e));
        assert!(!self.fixed_edges.contains(&e_));

        let a = self.vertex(Self::rot(e, 0));
        let b = self.vertex(Self::rot(e, 1));
        let c = self.vertex(Self::rot(e_, 0));
        let d = self.vertex(Self::rot(e_, 1));

        let da = self.adjacent(Self::rot(e, 1));
        let ab = self.adjacent(Self::rot(e, 2));
        let bc = self.adjacent(Self::rot(e_, 1));
        let cd = self.adjacent(Self::rot(e_, 2));

        // flip triangles
        *self.vertex_mut(Self::rot(e, 0)) = b;
        *self.vertex_mut(Self::rot(e, 1)) = c;
        *self.vertex_mut(Self::rot(e, 2)) = a;
        *self.vertex_mut(Self::rot(e_, 0)) = d;
        *self.vertex_mut(Self::rot(e_, 1)) = a;
        *self.vertex_mut(Self::rot(e_, 2)) = c;

        *self.adjacent_mut(Self::rot(e, 1)) = ab;
        *self.adjacent_mut(Self::rot(e, 2)) = bc;
        *self.adjacent_mut(Self::rot(e_, 1)) = cd;
        *self.adjacent_mut(Self::rot(e_, 2)) = da;

        // fix adjacencies
        if ab != Self::BD {
            *self.adjacent_mut(ab) = Self::rot(e, 1);
        }
        if bc != Self::BD {
            *self.adjacent_mut(bc) = Self::rot(e, 2);
        }
        if cd != Self::BD {
            *self.adjacent_mut(cd) = Self::rot(e_, 1);
        }
        if da != Self::BD {
            *self.adjacent_mut(da) = Self::rot(e_, 2);
        }

        // update grid
        // self.grid.insert(self.hashes[a], e/3);
        self.grid.insert(self.hashes[b], e / 3);
        // self.grid.insert(self.hashes[c], e_/3);
        self.grid.insert(self.hashes[d], e_ / 3);
    }

    fn add(&mut self, point: &Point) -> VIndex {
        let hash = self.hash(point);
        let p = self.points.len();
        self.points.push(*point);
        self.hashes.push(hash);

        let t = self.find(p).unwrap_err();

        // divide triangle
        let (e1, e2, e3) = {
            let [a, b, c] = self.vertices[t];
            let [bc, ca, ab] = self.adjacencies[t];
            // indices for new triangles
            let t1 = t;
            let t2 = self.vertices.len();
            let t3 = self.vertices.len() + 1;
            // add new triangles
            self.vertices[t] = [p, b, c];
            self.vertices.push([a, p, c]);
            self.vertices.push([a, b, p]);
            // add adjacency for new triangles
            self.adjacencies[t] = [bc, t2 * 3 + 0, t3 * 3 + 0];
            self.adjacencies.push([t1 * 3 + 1, ca, t3 * 3 + 1]);
            self.adjacencies.push([t1 * 3 + 2, t2 * 3 + 2, ab]);
            // modify adjacency for adjacent triangles
            if bc != Self::BD {
                *self.adjacent_mut(bc) = t1 * 3 + 0;
            }
            if ca != Self::BD {
                *self.adjacent_mut(ca) = t2 * 3 + 1;
            }
            if ab != Self::BD {
                *self.adjacent_mut(ab) = t3 * 3 + 2;
            }
            // update grid
            self.grid.insert(hash, t2);
            self.grid.insert(self.hashes[a], t2);
            // self.grid.insert(self.hashes[b], t1);
            // self.grid.insert(self.hashes[c], t1);
            (t1 * 3 + 0, t2 * 3 + 1, t3 * 3 + 2)
        };

        // fix star region
        let mut stack = vec![e1, e2, e3];
        while let Some(e) = stack.pop() {
            let e_ = self.adjacent(e);
            if e_ == Self::BD {
                continue;
            }
            if self.fixed_edges.contains(&e_) {
                continue;
            }

            // check if it is delaunay
            let a = self.vertex(Self::rot(e_, 0));
            let b = self.vertex(Self::rot(e_, 1));
            let c = self.vertex(Self::rot(e_, 2));
            if incirc(&self.points[a], &self.points[b], &self.points[c], point) != Ordering::Greater
            {
                continue;
            }

            // flip triangle
            self.flip(e);

            // add flipped triangles to stack
            stack.push(Self::rot(e, 2));
            stack.push(Self::rot(e_, 2));
        }

        p
    }

    // see: Computing 2D Constrained Delaunay Triangulation Using the GPU
    fn fix(&mut self, edge: &(VIndex, VIndex)) -> Option<(EIndex, EIndex)> {
        let start = &self.points[edge.0];
        let end = &self.points[edge.1];

        // find first intersected edge
        let e0 = {
            let t0 = self.find(edge.0).unwrap();
            let s = self.vertices[t0].iter().position(|v| v == &edge.0).unwrap();
            let e0: EIndex = t0 * 3 + s;
            let mut e = e0;
            loop {
                assert!(e != Self::BD);
                if self.vertex(Self::rot(e, 1)) == edge.1 {
                    let forward = Self::rot(e, 2);
                    let backward = self.adjacent(forward);
                    assert!(backward != Self::BD);
                    self.fixed_edges.insert(forward);
                    self.fixed_edges.insert(backward);
                    return Some((forward, backward));
                }
                if self.vertex(Self::rot(e, 2)) == edge.1 {
                    let backward = Self::rot(e, 1);
                    let forward = self.adjacent(backward);
                    assert!(forward != Self::BD);
                    self.fixed_edges.insert(forward);
                    self.fixed_edges.insert(backward);
                    return Some((forward, backward));
                }

                let a = self.vertex(Self::rot(e, 1));
                let b = self.vertex(Self::rot(e, 2));
                assert!(ori(&self.points[a], &self.points[b], start) == Ordering::Greater);
                if ori(end, start, &self.points[a]) == Ordering::Greater
                    && ori(start, end, &self.points[b]) == Ordering::Greater
                {
                    break;
                }

                assert!(self.adjacent(Self::rot(e, 1)) != Self::BD);
                e = Self::rot(self.adjacent(Self::rot(e, 1)), 1);

                assert!(e != e0);
            }
            e
        };

        // find sequence of intersected edges
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum PivotSide {
            Left,
            Right,
        }
        let mut crosses = {
            let mut crosses = vec![(PivotSide::Left, e0)];

            let mut e = e0;
            loop {
                let e_ = self.adjacent(e);
                let v = self.vertex(e_);
                if v == edge.1 {
                    break;
                }
                let s = if ori(start, end, &self.points[v]) == Ordering::Greater {
                    e = Self::rot(e_, 1);
                    PivotSide::Right
                } else {
                    e = Self::rot(e_, 2);
                    PivotSide::Left
                };
                assert!(self.adjacent(e) != Self::BD);
                crosses.push((s, e));
            }

            crosses
        };

        enum PairSide {
            Left,
            MiddleLeft,
            MiddleRight,
            Right,
        }
        let get_side = |crosses: &[(PivotSide, EIndex)], i: usize| -> PairSide {
            assert!(!crosses.is_empty());
            assert!(i < crosses.len());
            if i == 0 && i + 1 == crosses.len() {
                PairSide::Left
            } else if i == 0 {
                match crosses[i + 1].0 {
                    PivotSide::Left => PairSide::Right,
                    PivotSide::Right => PairSide::Left,
                }
            } else if i + 1 == crosses.len() {
                match crosses[i].0 {
                    PivotSide::Left => PairSide::Right,
                    PivotSide::Right => PairSide::Left,
                }
            } else {
                match (crosses[i].0, crosses[i + 1].0) {
                    (PivotSide::Left, PivotSide::Right) => PairSide::MiddleLeft,
                    (PivotSide::Right, PivotSide::Left) => PairSide::MiddleRight,
                    (PivotSide::Right, PivotSide::Right) => PairSide::Left,
                    (PivotSide::Left, PivotSide::Left) => PairSide::Right,
                }
            }
        };

        let (forward, backward, left_triangles, right_triangles) = {
            let mut i = 0usize;
            let mut left_triangles = Vec::<FIndex>::new();
            let mut right_triangles = Vec::<FIndex>::new();
            loop {
                assert!(i < crosses.len());

                // the vertices below this line form concave envelope
                assert!({
                    let mut left_vertices = Vec::<VIndex>::new();
                    let mut right_vertices = Vec::<VIndex>::new();

                    left_vertices.push(edge.0);
                    for (j, &(s, e)) in crosses[..=i].iter().enumerate() {
                        if j == 0 || s == PivotSide::Right {
                            left_vertices.push(self.vertex(Self::rot(e, 2)));
                        }
                    }

                    right_vertices.push(edge.0);
                    for (j, &(s, e)) in crosses[..=i].iter().enumerate() {
                        if j == 0 || s == PivotSide::Left {
                            right_vertices.push(self.vertex(Self::rot(e, 1)));
                        }
                    }

                    let test1 = left_vertices
                        .into_iter()
                        .map(|v| &self.points[v])
                        .collect::<Vec<&Point>>()
                        .windows(3)
                        .all(|t| ori(t[2], t[1], t[0]) == Ordering::Greater);
                    let test2 = right_vertices
                        .into_iter()
                        .map(|v| &self.points[v])
                        .collect::<Vec<&Point>>()
                        .windows(3)
                        .all(|t| ori(t[0], t[1], t[2]) == Ordering::Greater);
                    test1 && test2
                });

                match get_side(&crosses, i) {
                    PairSide::Left => {
                        let e = crosses[i].1;
                        let e_ = self.adjacent(e);
                        let a = self.vertex(Self::rot(e, 0));
                        let b = self.vertex(Self::rot(e_, 0));
                        let c = self.vertex(Self::rot(e_, 1));
                        if ori(&self.points[a], &self.points[b], &self.points[c])
                            == Ordering::Greater
                        {
                            self.flip(e);
                            left_triangles.push(e_ / 3);
                            if i + 1 < crosses.len() {
                                crosses[i + 1].1 = Self::rot(e, 2);
                            }
                            crosses.remove(i);
                            if crosses.is_empty() {
                                right_triangles.push(e / 3);
                                break (e_, e, left_triangles, right_triangles);
                            }
                        } else {
                            i += 1;
                        }
                    }
                    PairSide::Right => {
                        let e = crosses[i].1;
                        let e_ = self.adjacent(e);
                        let a = self.vertex(Self::rot(e_, 0));
                        let b = self.vertex(Self::rot(e, 0));
                        let c = self.vertex(Self::rot(e, 1));
                        if ori(&self.points[a], &self.points[b], &self.points[c])
                            == Ordering::Greater
                        {
                            self.flip(e);
                            right_triangles.push(e / 3);
                            if i + 1 < crosses.len() {
                                crosses[i + 1].1 = Self::rot(e_, 1);
                            }
                            crosses.remove(i);
                            if crosses.is_empty() {
                                left_triangles.push(e_ / 3);
                                break (e_, e, left_triangles, right_triangles);
                            }
                        } else {
                            i += 1;
                        }
                    }
                    PairSide::MiddleLeft => {
                        let e_prev = crosses[i - 1].1;
                        let e_next = crosses[i + 1].1;
                        let a = self.vertex(Self::rot(e_prev, 0));
                        let b = self.vertex(Self::rot(e_next, 2));
                        let c = self.vertex(Self::rot(e_next, 0));
                        if ori(&self.points[a], &self.points[b], &self.points[c])
                            == Ordering::Greater
                        {
                            let e = crosses[i].1;
                            let e_ = self.adjacent(e);
                            self.flip(e);
                            crosses[i] = (PivotSide::Right, e_);
                            crosses[i + 1] = (PivotSide::Left, Self::rot(e, 2));
                            i -= 1;
                        } else {
                            i += 1;
                        }
                    }
                    PairSide::MiddleRight => {
                        let e_prev = crosses[i - 1].1;
                        let e_next = crosses[i + 1].1;
                        let a = self.vertex(Self::rot(e_next, 1));
                        let b = self.vertex(Self::rot(e_prev, 0));
                        let c = self.vertex(Self::rot(e_next, 0));
                        if ori(&self.points[a], &self.points[b], &self.points[c])
                            == Ordering::Greater
                        {
                            let e = crosses[i].1;
                            let e_ = self.adjacent(e);
                            self.flip(e);
                            crosses[i] = (PivotSide::Left, e);
                            crosses[i + 1] = (PivotSide::Right, Self::rot(e_, 1));
                            i -= 1;
                        } else {
                            i += 1;
                        }
                    }
                }
            }
        };

        // re-delaunay
        let (forward, backward) = {
            let mut forward = forward;
            let mut backward = backward;
            for mut stack in [left_triangles, right_triangles] {
                while !stack.is_empty() {
                    let t = *stack.iter().next().unwrap();

                    let mut flipped = false;
                    for s in [0, 1, 2] {
                        let e: EIndex = t * 3 + s;
                        let e_ = self.adjacent(e);
                        if e_ == Self::BD || !stack.contains(&(e_ / 3)) {
                            continue;
                        }
                        let a = self.vertex(Self::rot(e, 2));
                        let b = self.vertex(Self::rot(e, 0));
                        let c = self.vertex(Self::rot(e, 1));
                        let d = self.vertex(e_);
                        if incirc(
                            &self.points[a],
                            &self.points[b],
                            &self.points[c],
                            &self.points[d],
                        ) == Ordering::Greater
                        {
                            self.flip(e);
                            if forward / 3 == e / 3 || forward / 3 == e_ / 3 {
                                forward = self.adjacent(backward);
                            }
                            if backward / 3 == e / 3 || backward / 3 == e_ / 3 {
                                backward = self.adjacent(forward);
                            }
                            flipped = true;
                            break;
                        }
                    }
                    if !flipped {
                        stack.remove(t);
                    }
                }
            }
            (forward, backward)
        };

        Some((forward, backward))
    }

    fn check(&self) -> bool {
        (0..self.vertices.len() * 3).all(|e| {
            let e_ = self.adjacent(e);
            if e_ == Self::BD {
                return true;
            }
            if self.fixed_edges.contains(&e) {
                return true;
            }
            let a = self.vertex(Self::rot(e, 2));
            let b = self.vertex(Self::rot(e, 0));
            let c = self.vertex(Self::rot(e, 1));
            let d = self.vertex(Self::rot(e_, 0));

            incirc(
                &self.points[a],
                &self.points[b],
                &self.points[c],
                &self.points[d],
            ) != Ordering::Greater
        })
    }

    fn get_triangles(&self) -> Vec<[VIndex; 3]> {
        // remove boundary
        self.vertices
            .iter()
            .cloned()
            .filter(|&[a, b, c]| a >= 4 && b >= 4 && c >= 4)
            .map(|[a, b, c]| [a - 4, b - 4, c - 4])
            .collect()
    }
}

pub fn delaunay(points: &[Point]) -> Vec<[VIndex; 3]> {
    assert!(points.iter().all(|&(x, y)| x.is_finite() && y.is_finite()));
    let bbox = {
        let x_min = points
            .iter()
            .map(|p| p.0)
            .reduce(|a, b| a.min(b))
            .unwrap_or(0.0);
        let y_min = points
            .iter()
            .map(|p| p.1)
            .reduce(|a, b| a.min(b))
            .unwrap_or(0.0);
        let x_max = points
            .iter()
            .map(|p| p.0)
            .reduce(|a, b| a.max(b))
            .unwrap_or(0.0);
        let y_max = points
            .iter()
            .map(|p| p.1)
            .reduce(|a, b| a.max(b))
            .unwrap_or(0.0);
        let width = (x_max - x_min).max(y_max - y_min).max(MIN_WIDTH);
        ((x_min, y_min), width)
    };
    let mut engine = Delaunay::new(bbox, points.len());
    for point in points {
        engine.add(point);
    }
    engine.get_triangles()
}

pub fn constrained_delaunay(
    points: &[Point],
    fixed_edges: &[(VIndex, VIndex)],
) -> Vec<[VIndex; 3]> {
    assert!(points.iter().all(|&(x, y)| x.is_finite() && y.is_finite()));
    let bbox = {
        let x_min = points
            .iter()
            .map(|p| p.0)
            .reduce(|a, b| a.min(b))
            .unwrap_or(0.0);
        let y_min = points
            .iter()
            .map(|p| p.1)
            .reduce(|a, b| a.min(b))
            .unwrap_or(0.0);
        let x_max = points
            .iter()
            .map(|p| p.0)
            .reduce(|a, b| a.max(b))
            .unwrap_or(0.0);
        let y_max = points
            .iter()
            .map(|p| p.1)
            .reduce(|a, b| a.max(b))
            .unwrap_or(0.0);
        let width = (x_max - x_min).max(y_max - y_min).max(MIN_WIDTH);
        ((x_min, y_min), width)
    };
    let mut engine = Delaunay::new(bbox, points.len());
    let mut map = HashMap::<usize, usize>::new();
    for (i, point) in points.iter().enumerate() {
        let j = engine.add(point);
        map.insert(i, j);
    }
    for (a, b) in fixed_edges {
        let a = *map.get(a).unwrap();
        let b = *map.get(b).unwrap();
        engine.fix(&(a, b));
    }
    engine.get_triangles()
}
