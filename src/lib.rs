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

impl<I: FallibleIterator + ?Sized> FallibleIterator for Box<I> {
    type Item = I::Item;
    type Error = I::Error;

    fn next(&mut self) -> Result<Option<I::Item>, I::Error> {
        (**self).next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }
}

pub trait DoubleEndedFallibleIterator: FallibleIterator {
    fn next_back(&mut self) -> Result<Option<Self::Item>, Self::Error>;

    fn rev(self) -> Rev<Self> where Self: Sized {
        Rev(self)
    }
}

pub fn convert<T, E, I>(it: I) -> Convert<I> where I: Iterator<Item = Result<T, E>> {
    Convert(it)
}

pub struct Convert<I>(I);

impl<T, E, I: Iterator<Item = Result<T, E>>> FallibleIterator for Convert<I> {
    type Item = T;
    type Error = E;

    fn next(&mut self) -> Result<Option<T>, E> {
        match self.0.next() {
            Some(Ok(i)) => Ok(Some(i)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

pub struct Rev<I>(I);

impl<I> FallibleIterator for Rev<I> where I: DoubleEndedFallibleIterator {
    type Item = I::Item;
    type Error = I::Error;

    fn next(&mut self) -> Result<Option<I::Item>, I::Error> {
        self.0.next_back()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn count(self) -> Result<usize, I::Error> {
        self.0.count()
    }
}

impl<I> DoubleEndedFallibleIterator for Rev<I> where I: DoubleEndedFallibleIterator {
    fn next_back(&mut self) -> Result<Option<I::Item>, I::Error> {
        self.0.next()
    }
}
