pub trait FallibleIterator {
    type Item;
    type Error;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }

    fn count(mut self) -> Result<usize, Self::Error> where Self: Sized {
        let mut count = 0;
        while let Some(_) = try!(self.next()) {
            count += 1;
        }

        Ok(count)
    }
}

impl<T, E, I: Iterator<Item = Result<T, E>>> FallibleIterator for I {
    type Item = T;
    type Error = E;

    fn next(&mut self) -> Result<Option<T>, E> {
        match Iterator::next(self) {
            Some(Ok(i)) => Ok(Some(i)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        Iterator::size_hint(self)
    }
}
