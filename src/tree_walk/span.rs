use std::fmt::Display;
use std::ops::{Add, AddAssign, Deref};

use crate::tree_walk::error::{RuntimeError, ThrowRuntimeError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span {
    /// Offset where the span starts
    pub offset: usize,
    /// Span length
    pub length: usize,
    /// Line number (including comments)
    pub lineno: usize,
    /// Offset where the line starts
    pub lineof: usize,
}

impl Span {
    pub const SNIPPET_LIMIT: usize = 60;

    pub(crate) const fn empty() -> Self {
        Self {
            offset: 0,
            length: 0,
            lineno: 0,
            lineof: 0,
        }
    }

    /// ```
    /// # use codcrafters_interpreter_rust::span::Span;
    /// let s = Span { offset: 2, length: 6, lineno: 0, lineof: 10 };
    /// assert_eq!(s.end(), 8);
    /// ```
    #[inline]
    pub fn end(&self) -> usize {
        self.offset + self.length
    }

    /// Position within the line of where the span starts
    #[inline]
    pub fn column(&self) -> usize {
        self.offset - self.lineof
    }

    #[inline]
    pub fn loc(&self) -> SpanLoc<'_> {
        SpanLoc(self)
    }

    /// Take a snippet of the `src` code at the location represented by this span
    ///
    /// Note that the snippet length is limited to [`SNIPPET_LIMIT`](Self::SNIPPET_LIMIT)
    /// characters.
    pub fn snippet<'a>(&self, src: &'a str) -> &'a str {
        let s = &src[self.offset..self.end()];
        &s[..s.len().min(Self::SNIPPET_LIMIT)]
    }
}

impl Add<Span> for Span {
    type Output = Span;

    /// ```
    /// # use codcrafters_interpreter_rust::span::Span;
    /// let s1 = Span { offset: 0, length: 6, lineno: 0, lineof: 0 };
    /// let s2 = Span { offset: 7, length: 3, lineno: 0, lineof: 0 };
    /// let s3 = s1 + s2;
    /// assert_eq!(&s3, &Span { offset: 0, length: 10, lineno: 0, lineof: 0 });
    /// assert_eq!(s3.end(), 10);
    ///
    /// let s1 = Span { offset: 2, length: 6, lineno: 0, lineof: 1 };
    /// let s2 = Span { offset: 14, length: 3, lineno: 1, lineof: 0 };
    /// let s3 = s1 + s2;
    /// assert_eq!(&s3, &Span { offset: 2, length: 15, lineno: 0, lineof: 1 });
    /// assert_eq!(s3.end(), 17);
    /// ```
    fn add(self, other: Span) -> Self::Output {
        self + &other
    }
}

impl<S: Deref<Target = Span>> Add<S> for Span {
    type Output = Span;

    fn add(mut self, other: S) -> Self::Output {
        self += other;
        self
    }
}

impl Add for &Span {
    type Output = Span;

    fn add(self, other: Self) -> Self::Output {
        debug_assert!(self.end() <= other.offset);
        debug_assert!(self.lineno <= other.lineno);
        Span {
            length: self.length + (other.offset - self.end()) + other.length,
            ..*self
        }
    }
}

impl AddAssign<Span> for Span {
    #[inline]
    fn add_assign(&mut self, other: Span) {
        self.add_assign(&other)
    }
}

impl<S: Deref<Target = Span>> AddAssign<S> for Span {
    fn add_assign(&mut self, other: S) {
        debug_assert!(self.end() <= other.offset);
        debug_assert!(self.lineno <= other.lineno);
        self.length += (other.offset - self.end()) + other.length;
    }
}

impl ThrowRuntimeError for Span {
    #[inline]
    fn throw(&self, msg: impl Display) -> RuntimeError {
        RuntimeError {
            span: self.clone(),
            source: msg.to_string().into(),
        }
    }
}

pub struct SpanLoc<'s>(&'s Span);

impl Display for SpanLoc<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.0.lineno, self.0.column(), self.0.length)
    }
}
