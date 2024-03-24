use std::{collections::{BTreeSet, HashSet}, fs::File, io::{self, Write}};

use ordered_float::NotNan;

mod incr;

fn save_ply(points: &[(f32, f32)], triangles: &[[usize; 3]], filepath: &str) -> io::Result<()> {
    let mut file = File::create(filepath)?;
    file.write_all(format!("
ply
format ascii 1.0
element vertex {}
property float x
property float y
property float z
element face {}
property list uchar uint vertex_indices
end_header
", points.len(), triangles.len()).trim_start().as_bytes())?;
    for point in points {
        file.write_all(format!("{} {} 0.0\n", point.0, point.1).as_bytes())?;
    }
    for triangle in triangles {
        file.write_all(format!("3 {} {} {}\n", triangle[0], triangle[1], triangle[2]).as_bytes())?;
    }
    Ok(())
}

fn timing<R, F: FnOnce() -> R>(f: F) -> R {
    let now = std::time::Instant::now();
    let res = f();
    let elapse = now.elapsed();
    println!("elapse = {:?}", elapse);
    res
}

const POINT_COUNT: usize = 100;

fn main() {
    // prepare random, distinct, finite points
    println!("prepare data...");
    let points = timing(||
        (0..POINT_COUNT)
            .map(|_| rand::random::<(f32, f32)>())
            .map(|(x, y)| (NotNan::new(x).unwrap(), NotNan::new(y).unwrap()))
            .collect::<HashSet<_>>()
            // .collect::<BTreeSet<_>>() // sorted points are performed better for delaunay somehow
            .into_iter()
            .map(|(x, y)| (x.into_inner(), y.into_inner()))
            .collect::<Vec<_>>()
    );
    println!("point count = {}", points.len());

    println!("run delaunay...");
    let triangles = timing(|| incr::delaunay(&points));

    println!("save to test.ply...");
    save_ply(&points, &triangles, "test.ply").expect("fail to write file test.ply");
}
