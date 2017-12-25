use core::iter;

use super::{convert, FallibleIterator, Vec};

#[test]
fn all() {
    assert!(convert([0, 1, 2, 3].iter().map(Ok::<&u32, ()>)).all(|&i| i < 4).unwrap());
    assert!(!convert([0, 1, 2, 4].iter().map(Ok::<&u32, ()>)).all(|&i| i < 4).unwrap());
}

#[test]
fn and_then() {
    let it = convert(vec![0, 1, 2, 3, 4].into_iter().map(Ok::<u32, ()>)).and_then(|n| Ok(n * 2));
    assert_eq!(it.collect::<Vec<_>>().unwrap(), [0, 2, 4, 6, 8]);

    let mut it = convert(vec![0, 1, 2, 3, 4].into_iter().map(Ok::<u32, ()>))
        .and_then(|n| {
            if n == 2 {
                Err(())
            } else {
                Ok(n * 2)
            }
        });
    assert_eq!(it.next().unwrap().unwrap(), 0);
    assert_eq!(it.next().unwrap().unwrap(), 2);
    assert_eq!(it.next(), Err(()));
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

#[test]
fn filter() {
    let it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>)).filter(|&x| x % 2 == 0);

    assert_eq!(it.collect::<Vec<_>>().unwrap(), [0, 2]);
}

#[test]
fn filter_map() {
    let it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>))
        .filter_map(|x| {
            if x % 2 == 0 {
                Some(x + 1)
            } else {
                None
            }
        });

    assert_eq!(it.collect::<Vec<_>>().unwrap(), [1, 3]);
}

#[test]
fn find() {
    let mut it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>));

    assert_eq!(it.find(|x| x % 2 == 1).unwrap(), Some(1));
    assert_eq!(it.next().unwrap(), Some(2));
}

#[test]
fn fold() {
    let it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>));
    assert_eq!(it.fold(0, |a, b| a + b).unwrap(), 6);
}

#[test]
fn last() {
    let it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<u32, ()>));
    assert_eq!(it.last().unwrap(), Some(3));
}

#[test]
fn max() {
    let it = convert(vec![0, 3, 1, -10].into_iter().map(Ok::<i32, ()>));
    assert_eq!(it.max().unwrap(), Some(3));
}

#[test]
fn max_by_key() {
    let it = convert(vec![0, 3, 1, -10].into_iter().map(Ok::<i32, ()>));
    assert_eq!(it.max_by_key(|&i| -i).unwrap(), Some(-10));
}

#[test]
fn min() {
    let it = convert(vec![0, 3, -10, 1].into_iter().map(Ok::<i32, ()>));
    assert_eq!(it.min().unwrap(), Some(-10));
}

#[test]
fn min_by_key() {
    let it = convert(vec![0, 3, 1, -10].into_iter().map(Ok::<i32, ()>));
    assert_eq!(it.min_by_key(|&i| -i).unwrap(), Some(3));
}

#[test]
fn nth() {
    let mut it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<i32, ()>));
    assert_eq!(it.nth(1).unwrap(), Some(1));
    assert_eq!(it.nth(0).unwrap(), Some(2));
    assert_eq!(it.nth(2).unwrap(), None);
}

#[test]
fn peekable() {
    let mut it = convert(vec![0, 1].into_iter().map(Ok::<i32, ()>)).peekable();
    assert_eq!(it.peek().unwrap(), Some(&0));
    assert_eq!(it.peek().unwrap(), Some(&0));
    assert_eq!(it.next().unwrap(), Some(0));
    assert_eq!(it.next().unwrap(), Some(1));
    assert_eq!(it.peek().unwrap(), None);
    assert_eq!(it.next().unwrap(), None);
}

#[test]
fn position() {
    let mut it = convert(vec![1, 2, 3, 4].into_iter().map(Ok::<i32, ()>));
    assert_eq!(it.position(|n| n == 2).unwrap(), Some(1));
    assert_eq!(it.position(|n| n == 3).unwrap(), Some(0));
    assert_eq!(it.position(|n| n == 5).unwrap(), None);
}

#[test]
fn take() {
    let it = convert(vec![0, 1, 2, 3].into_iter().map(Ok::<i32, ()>)).take(2);
    assert_eq!(it.collect::<Vec<_>>().unwrap(), [0, 1]);
}
