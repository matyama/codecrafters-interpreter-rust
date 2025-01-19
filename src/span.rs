use std::fmt::Display;
use std::ops::{Add, AddAssign, Deref};

use crate::error::{RuntimeError, ThrowRuntimeError};

/// Span represents a line and range information about a piece of source code.
///
/// # Representation
/// Logically, the span is a 4-tuple composed of the following:
///  1. The line number
///  2. The byte offset where the line starts
///  3. The byte offset where the span starts
///  4. The length (in the number of bytes) of the span
///
/// # Encoding
/// For efficiency reasons, the span is encoded as a single `u128` number where each of the logical
/// parts forms one `u32` segment. That is, the segments can be visualized as:
/// ```
/// [lineno, lineof, offset, length]
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Span(u128);

impl Span {
    pub const SNIPPET_LIMIT: usize = 60;

    #[inline]
    pub(crate) const fn empty() -> Self {
        Self(0)
    }

    /// Derive a simplified span which only carries the line number.
    #[inline]
    pub const fn line(lineno: u32) -> Self {
        Self::new(0, 0, lineno, 0)
    }

    #[inline]
    pub const fn new(offset: u32, length: u32, lineno: u32, lineof: u32) -> Self {
        Self({
            length as u128
                | (offset as u128) << 32
                | (lineof as u128) << 64
                | (lineno as u128) << 96
        })
    }

    /// Line number (including comments)
    #[inline]
    pub const fn lineno(&self) -> u32 {
        (self.0 >> 96) as u32
    }

    /// Offset where the line starts
    #[inline]
    pub const fn lineof(&self) -> u32 {
        (self.0 >> 64) as u32
    }

    /// Offset where the span starts
    #[inline]
    pub const fn offset(&self) -> u32 {
        (self.0 >> 32) as u32
    }

    /// Span length
    #[inline]
    pub const fn length(&self) -> u32 {
        self.0 as u32
    }

    #[inline]
    pub const fn end(&self) -> u32 {
        self.offset() + self.length()
    }

    /// Position within the line of where the span starts
    #[inline]
    pub const fn column(&self) -> u32 {
        self.offset() - self.lineof()
    }

    #[inline]
    pub const fn loc(&self) -> SpanLoc<'_> {
        SpanLoc(self)
    }

    /// Take a snippet of the `src` code at the location represented by this span
    ///
    /// Note that the snippet length is limited to [`SNIPPET_LIMIT`](Self::SNIPPET_LIMIT)
    /// characters.
    pub fn snippet<'a>(&self, src: &'a str) -> &'a str {
        let s = &src[self.offset() as usize..self.end() as usize];
        &s[..s.len().min(Self::SNIPPET_LIMIT)]
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Span")
            .field("lineno", &self.lineno())
            .field("lineof", &self.lineof())
            .field("offset", &self.offset())
            .field("length", &self.length())
            .finish()
    }
}

impl Add<Span> for Span {
    type Output = Span;

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
        debug_assert!(self.end() <= other.offset());
        debug_assert!(self.lineno() <= other.lineno());
        let length = self.length() + (other.offset() - self.end()) + other.length();
        // first clear the old length and then set the updated one
        Span((self.0 >> 32) << 32 | length as u128)
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
        debug_assert!(self.end() <= other.offset());
        debug_assert!(self.lineno() <= other.lineno());
        let length = self.length() + (other.offset() - self.end()) + other.length();
        // clear the old length
        self.0 >>= 32;
        self.0 <<= 32;
        // set the updated length
        self.0 |= length as u128;
    }
}

impl ThrowRuntimeError for Span {
    #[inline]
    fn throw(&self, msg: impl Display) -> RuntimeError {
        RuntimeError {
            span: *self,
            source: msg.to_string().into(),
        }
    }
}

pub struct SpanLoc<'s>(&'s Span);

impl Deref for SpanLoc<'_> {
    type Target = Span;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl Display for SpanLoc<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.lineno(), self.column(), self.length())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn end_offset() {
        let s = Span::new(2, 6, 0, 10);
        assert_eq!(s.end(), 8);
    }

    #[test]
    fn extend_same_line() {
        let s1 = Span::new(0, 6, 0, 0);
        let s2 = Span::new(7, 3, 0, 0);
        let s3 = s1 + s2;
        let expected = Span::new(0, 10, 0, 0);
        assert_eq!(&s3, &expected, "{s3} != {expected}");
        assert_eq!(s3.end(), 10);
    }

    #[test]
    fn extend_different_line() {
        let s1 = Span::new(2, 6, 0, 1);
        let s2 = Span::new(14, 3, 1, 0);
        let s3 = s1 + s2;
        let expected = Span::new(2, 15, 0, 1);
        assert_eq!(&s3, &expected, "{s3} != {expected}");
        assert_eq!(s3.end(), 17);
    }

    #[test]
    fn display_location() {
        let s = Span::new(14, 15, 2, 10);
        assert_eq!("2:4:15", s.loc().to_string());
    }

    #[test]
    fn derive_line_span() {
        let expected = Span::new(0, 0, 2, 0);
        let actual = Span::line(2);
        assert_eq!(expected, actual, "{expected} != {actual}");
    }
}
