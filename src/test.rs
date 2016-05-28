use std::iter;

use super::{convert, FallibleIterator};

#[test]
fn all() {
    assert!(convert([0, 1, 2, 3].iter().map(Ok::<&u32, ()>)).all(|&i| i < 4).unwrap());
    assert!(!convert([0, 1, 2, 4].iter().map(Ok::<&u32, ()>)).all(|&i| i < 4).unwrap());
}

#[test]
fn any() {
    assert!(convert([0, 1, 2, 3].iter().map(Ok::<&u32, ()>)).any(|&i| i == 3).unwrap());
    assert!(!convert([0, 1, 2, 4].iter().map(Ok::<&u32, ()>)).any(|&i| i == 3).unwrap());
}

#[test]
fn chain() {
    let a = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>));
    let b = convert(vec![4, 5, 6, 7].into_iter().map(Ok::<u32, ()>));
    let it = a.chain(b);

    assert_eq!(it.collect::<Vec<_>>().unwrap(), [0, 1, 2, 3, 4, 5, 6, 7]);

    let a = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>));
    let b = convert(vec![4, 5, 6, 7].into_iter().map(Ok::<u32, ()>));
    let it = a.chain(b).rev();

    assert_eq!(it.collect::<Vec<_>>().unwrap(), [7, 6, 5, 4, 3, 2, 1, 0]);
}

#[test]
fn count() {
    assert_eq!(convert([0, 1, 2, 3].iter().map(Ok::<&u32, ()>)).count().unwrap(), 4);

    let it = Some(Ok(1)).into_iter().chain(iter::repeat(Err(())));
    assert!(convert(it).count().is_err());
}

#[test]
fn enumerate() {
    let it = convert(vec![5, 6, 7, 8].into_iter().map(Ok::<u32, ()>)).enumerate();

    assert_eq!(it.collect::<Vec<_>>().unwrap(), [(0, 5), (1, 6), (2, 7), (3, 8)]);
}
