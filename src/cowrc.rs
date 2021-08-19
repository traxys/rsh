use std::{borrow::Borrow, fmt, ops::Deref, rc::Rc};

pub enum CowRc<'a, B>
where
    B: ToOwned + ?Sized,
{
    Borrowed(&'a B),
    Shared(Rc<B::Owned>),
}

impl<B: ?Sized + ToOwned> Deref for CowRc<'_, B> {
    type Target = B;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Borrowed(b) => b,
            Self::Shared(shared) => shared.as_ref().borrow(),
        }
    }
}

impl<T: ?Sized + ToOwned> AsRef<T> for CowRc<'_, T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<B: ?Sized + ToOwned> Clone for CowRc<'_, B> {
    fn clone(&self) -> Self {
        match self {
            Self::Borrowed(b) => Self::Borrowed(b),
            Self::Shared(o) => {
                let b: &B = o.as_ref().borrow();
                Self::Shared(Rc::new(b.to_owned()))
            }
        }
    }
}

impl<'a, 'b, B: ?Sized, C: ?Sized> PartialEq<CowRc<'b, C>> for CowRc<'a, B>
where
    B: PartialEq<C> + ToOwned,
    C: ToOwned,
{
    #[inline]
    fn eq(&self, other: &CowRc<'b, C>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}

impl<B: ?Sized> Eq for CowRc<'_, B> where B: Eq + ToOwned {}

impl From<String> for CowRc<'_, str> {
    fn from(v: String) -> Self {
        Self::Shared(Rc::new(v))
    }
}

impl<B: ?Sized, D> fmt::Debug for CowRc<'_, B>
where
    B: fmt::Debug + ToOwned<Owned = D>,
    D: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Borrowed(b) => fmt::Debug::fmt(b, f),
            Self::Shared(o) => fmt::Debug::fmt(o.as_ref(), f),
        }
    }
}

impl<B: ?Sized, D> fmt::Display for CowRc<'_, B>
where
    B: fmt::Display + ToOwned<Owned = D>,
    D: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Borrowed(b) => fmt::Display::fmt(b, f),
            Self::Shared(o) => fmt::Display::fmt(o.as_ref(), f),
        }
    }
}

impl<'a> From<&'a str> for CowRc<'a, str> {
    fn from(v: &'a str) -> Self {
        CowRc::Borrowed(v)
    }
}
