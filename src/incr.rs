#![allow(dead_code)]
#![allow(clippy::identity_op)]
#![allow(clippy::erasing_op)]

use std::{cmp::{min_by_key, Ordering}, collections::BTreeMap};

/// returns Greater if c is on the left side of the line a -> b,
/// or Equal if is on the line, or Less if is on the right side.
fn ori(a: &(f32, f32), b: &(f32, f32), c: &(f32, f32)) -> Ordering {
    let ca = (a.0 - c.0, a.1 - c.1);
    let cb = (b.0 - c.0, b.1 - c.1);

    // deal with infinite points
    let ca = if ca.0.is_infinite() { (ca.0.signum(), ca.1.signum()) } else { ca };
    let cb = if cb.0.is_infinite() { (cb.0.signum(), cb.1.signum()) } else { cb };

    (ca.0 * cb.1 - ca.1 * cb.0).partial_cmp(&0.0).unwrap()
}

/// returns 3 if p is inside the triangle or on the edge,
/// or 0, 1, 2 if p is outside this side of the triangle.
fn triside(a: &(f32, f32), b: &(f32, f32), c: &(f32, f32), p: &(f32, f32)) -> usize {
    if ori(b, c, p).is_lt() {
        return 0;
    }
    if ori(c, a, p).is_lt() {
        return 1;
    }
    if ori(a, b, p).is_lt() {
        return 2;
    }
    3
}

/// returns Greater if d is in the circumcircle of a, b, c,
/// or Equal if is on the circle, or Less if is outside the circle.
fn incirc(a: &(f32, f32), b: &(f32, f32), c: &(f32, f32), d: &(f32, f32)) -> Ordering {
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
// const CORNER1: (f32, f32) = (-1e5, -1e5);
// const CORNER2: (f32, f32) = ( 1e5, -1e5);
// const CORNER3: (f32, f32) = ( 1e5,  1e5);
// const CORNER4: (f32, f32) = (-1e5,  1e5);
const CORNER1: (f32, f32) = (-f32::INFINITY, -f32::INFINITY);
const CORNER2: (f32, f32) = ( f32::INFINITY, -f32::INFINITY);
const CORNER3: (f32, f32) = ( f32::INFINITY,  f32::INFINITY);
const CORNER4: (f32, f32) = (-f32::INFINITY,  f32::INFINITY);

const MIN_WIDTH: f32 = 1e-5;
const HASH_SIZE: u32 = 8;

pub fn delaunay(points: &[(f32, f32)]) -> Vec<[usize; 3]> {
    assert!(points.iter().all(|&(x, y)| x.is_finite() && y.is_finite()));
    
    let len = points.len();
    let points = {
        // normalize
        let x_min = points.iter().map(|p| p.0).reduce(|a, b| a.min(b)).unwrap_or(0.0);
        let y_min = points.iter().map(|p| p.1).reduce(|a, b| a.min(b)).unwrap_or(0.0);
        let x_max = points.iter().map(|p| p.0).reduce(|a, b| a.max(b)).unwrap_or(0.0);
        let y_max = points.iter().map(|p| p.1).reduce(|a, b| a.max(b)).unwrap_or(0.0);
        let width = (x_max - x_min).max(y_max - y_min).max(MIN_WIDTH);
        points.iter()
            .map(|&(x, y)| ((x - x_min) / width, (y - y_min) / width))
            .chain([CORNER1, CORNER2, CORNER3, CORNER4])
            .collect::<Vec<_>>()
    };
    let hashes = points.iter().map(|&(x, y)| hilbert_dist::<HASH_SIZE>(x, y)).collect::<Vec<_>>();

    const BD: usize = usize::MAX;
    //             [a_index, b_index, c_index]
    let mut triangles: Vec<[usize; 3]> = vec![[len+0, len+1, len+2], [len+2, len+3, len+0]];
    triangles.reserve(len * 2);
    //               [bc_adj, ca_adj, ab_adj],  adj = tri_index * 3 + side or BD for unmovable edge
    let mut adjacency: Vec<[usize; 3]> = vec![[BD, 1*3+1, BD], [BD, 0*3+1, BD]];
    //                  hash -> tri_index,  each hash indicates a grid region
    adjacency.reserve(len * 2);
    let mut grid: BTreeMap<u32, usize> = BTreeMap::new();
    grid.insert(hashes[len+0], 0);
    grid.insert(hashes[len+1], 0);
    grid.insert(hashes[len+2], 1);
    grid.insert(hashes[len+3], 1);

    for p in 0..len {
        let point = &points[p];
        let hash = hashes[p];

        // find triangle contains points[i]
        let t = {
            // find the nearest triangle in the grid
            let mut t = *min_by_key(
                grid.range(hash..).next(),
                grid.range(..hash).next_back(),
                |e| e.map(|(h, _)| h.abs_diff(hash)).unwrap_or(u32::MAX),
            ).unwrap().1;
            // walk to the point
            loop {
                let [a, b, c] = triangles[t];
                let side = triside(&points[a], &points[b], &points[c], point);
                if side == 3 { break; }
                let edge = adjacency[t][side];
                if edge == BD {
                    panic!("invalid");
                }
                t = edge / 3;
            }
            t
        };

        // divide triangle
        let (e1, e2, e3) = {
            let [a, b, c] = triangles[t];
            let [bc, ca, ab] = adjacency[t];
            // indices for new triangles
            let t1 = t;
            let t2 = triangles.len();
            let t3 = triangles.len() + 1;
            // add new triangles
            triangles[t] = [p, b, c];
            triangles.push([a, p, c]);
            triangles.push([a, b, p]);
            // add adjacency for new triangles
            adjacency[t] = [bc, t2*3+0, t3*3+0];
            adjacency.push([t1*3+1, ca, t3*3+1]);
            adjacency.push([t1*3+2, t2*3+2, ab]);
            // modify adjacency for adjacent triangles
            if bc != BD { adjacency[bc/3][bc%3] = t1*3+0; }
            if ca != BD { adjacency[ca/3][ca%3] = t2*3+1; }
            if ab != BD { adjacency[ab/3][ab%3] = t3*3+2; }
            // update grid
            grid.insert(hash, t2);
            grid.insert(hashes[a], t2);
            // grid.insert(hashes[b], t1);
            // grid.insert(hashes[c], t1);
            (t1*3+0, t2*3+1, t3*3+2)
        };

        // fix star region
        let mut stack = vec![e1, e2, e3];
        while let Some(e) = stack.pop() {
            let (tri, side) = (e / 3, e % 3);
            let e_ = adjacency[tri][side];
            if e_ == BD { continue; }
            let (tri_, side_) = (e_ / 3, e_ % 3);

            // check if it is delaunay
            let [a, b, c] = triangles[tri_];
            if incirc(&points[a], &points[b], &points[c], point) != Ordering::Greater {
                continue;
            }

            // flip triangle
            
            let a = triangles[tri][side];
            let b = triangles[tri][(side + 1) % 3];
            let c = triangles[tri_][side_];
            let d = triangles[tri_][(side_ + 1) % 3];

            let da = adjacency[tri][(side + 1) % 3];
            let ab = adjacency[tri][(side + 2) % 3];
            let bc = adjacency[tri_][(side_ + 1) % 3];
            let cd = adjacency[tri_][(side_ + 2) % 3];

            // flip triangles
            triangles[tri] = [a, b, c];
            triangles[tri_] = [c, d, a];
            adjacency[tri] = [bc, tri_*3+1, ab];
            adjacency[tri_] = [da, tri*3+1, cd];
            // fix adjacencies
            if ab != BD { adjacency[ab/3][ab%3] = tri*3+2; }
            if bc != BD { adjacency[bc/3][bc%3] = tri*3+0; }
            if cd != BD { adjacency[cd/3][cd%3] = tri_*3+2; }
            if da != BD { adjacency[da/3][da%3] = tri_*3+0; }
            // update grid
            grid.insert(hashes[a], tri);
            grid.insert(hashes[b], tri);
            grid.insert(hashes[c], tri_);
            grid.insert(hashes[d], tri_);

            // add flipped triangles to stack
            stack.push(tri*3+0);
            stack.push(tri_*3+2);
        }
    }
    
    // remove boundary
    triangles.into_iter().filter(|&[a, b, c]| a < len && b < len && c < len).collect()
}
