//! Encapsulates the concept of a substring of a certain length found at a
//! given offset, which can be useful when this information cannot be directly
//! coupled to the lifetime of the orignal string it was derived from. This can
//! be useful, for example, when the section of a string which caused a parsing
//! error must be reported in a manner which must survive the lifetime of the
//! original parsed string.
//! 
//! This may sound like an odd set of requirements, but it notably occurs when
//! implementing an external trait (which cannot be modified to take a lifetime
//! parameter) which contains a function which takes a `&str` -- like, say,
//! `std::str::FromStr`.

use std::{cmp::Ordering, ops::Range};

/// A `Substr` represents the position of a child string within a parent, and
/// can be converted back to its original form if the parent `&str` it was
/// derived from is still avaliable.
#[derive(Copy, Clone, Debug)]
pub struct Substr {
    offset: usize,
    length: usize,
}

impl Default for Substr {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl From<Range<usize>> for Substr {
    fn from(r: Range<usize>) -> Self {
        if r.start < r.end {
            Self {
                offset: r.start,
                length: (r.end - r.start),
            }
        } else {
            Self::EMPTY
        }
    }
}

impl PartialEq for Substr {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

/// Two Substr instances are considered equal if they are both empty or both refer to the same section of a string.
impl PartialOrd for Substr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let c = self.length.cmp(&other.length);
        if c != Ordering::Equal {
            Some(c)
        } else {
            if self.length == 0 || self.offset == other.offset {
                Some(Ordering::Equal)
            } else {
                None
            }
        }
    }
}

impl Substr {
    const EMPTY: Self = Self {
        offset: 0,
        length: 0,
    };

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Creates a Substr by finding the child within the parent. If the child
    /// str points to a range wholly contained within the parent, this will use
    /// pointer arithmetic and be O(1); if not, `str::find` will be used, which
    /// is linear in the size of the parent.
    pub fn make(parent: &str, child: &str) -> Result<Self, ()> {
        if child.is_empty() {
            return Ok(Self::EMPTY);
        }
        let p = parent.as_ptr() as usize;
        let c = child.as_ptr() as usize;
        if c >= p && c + child.len() < p + parent.len() {
            Ok(Self {
                offset: c - p,
                length: child.len(),
            })
        } else {
            if let Some(i) = parent.find(child) {
                Ok(Self {
                    offset: i,
                    length: child.len(),
                })
            } else {
                Err(())
            }
        }
    }

    /// Recovers a `&str` from a Substr. The provided parent must be at least
    /// as long as `offset + length`.
    /// 
    /// The recovered `&str` is guaranteed to point to the same slice of memory
    /// as the orignal if the same parent is provided. The recovered `&str` is
    /// guaranteed to compare equal to the original if the substring
    /// `[offset, offset + length)` of the provided parent compares equal to the
    /// same substring of the original parent.
    /// 
    /// # Panics
    /// 
    /// Panics if `length` or `length + offset` within the provided parent is
    /// not on a UTF-8 code point boundary.
    pub fn recover<'a>(&self, parent: &'a str) -> Result<&'a str, ()> {
        if self.offset + self.length <= parent.len() {
            Ok(parent.split_at(self.offset).1.split_at(self.length).0)
        } else {
            Err(())
        }
    }
}

impl From<Substr> for Range<usize> {
    fn from(s: Substr) -> Self {
        Self{
            start: s.offset,
            end: s.offset + s.length,
        }
    }
}

/// A helper trait to make converting a `&str` to a `Substr` easier. Returns an
/// `Option` instead of a `Result` to match the behavior of `str::find()`.
pub trait FindSubstr: {
    fn find_substr(&self, s: &str) -> Option<Substr>;
}

impl FindSubstr for str {
    fn find_substr(&self, s: &str) -> Option<Substr> {
        Substr::make(self, s).ok()
    }
}

/// Handy default `Substr` whose length and offset are both zero. Returned via
/// `Substr::default()`.
pub const EMPTY: Substr = Substr::EMPTY;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_equality() {
        assert_eq!(EMPTY, Substr{
            offset: 0,
            length: 0,
        });
        assert_eq!(EMPTY, Substr{
            offset: 42,
            length: 0,
        });
        assert_ne!(EMPTY, Substr{
            offset: 0,
            length: 42,
        });
    }

    #[test]
    fn roundtrip_with_contained_child() -> Result<(), ()> {
        let foobar = "foobar";
        let (foo, bar) = foobar.split_at(3);
        let empty = foobar.split_at(0).0;

        assert_eq!(Substr::make(foobar, foo)?.recover(foobar)?, "foo");
        assert_eq!(Substr::make(foobar, bar)?.recover(foobar)?, "bar");
        assert_eq!(Substr::make(foobar, empty)?.recover(foobar)?, "");
        Ok(())
    }

    #[test]
    fn roundtrip_preserves_ptr() -> Result<(), ()> {
        let foobar = "foobar";
        let (foo, bar) = foobar.split_at(3);

        let foo_rec = Substr::make(foobar, foo)?.recover(foobar)?;
        assert_eq!(foo_rec.as_ptr(), foo.as_ptr());

        let bar_rec = Substr::make(foobar, bar)?.recover(foobar)?;
        assert_eq!(bar_rec.as_ptr(), bar.as_ptr());
        Ok(())
    }

    #[test]
    fn roundtrip_without_contained_child() -> Result<(), ()> {
        let foobar = "foobar";
        let foo = "foo1".split_at(3).0;
        let bar = "bar1".split_at(3).0;

        assert_eq!(Substr::make(foobar, foo)?.recover(foobar)?, "foo");
        assert_eq!(Substr::make(foobar, bar)?.recover(foobar)?, "bar");
        Ok(())
    }

    #[test]
    fn roundtrip_with_different_parent() -> Result<(), ()> {
        let foobar1 = "foobar1";
        let foobar2 = "foobar2";
        let foo = "foo";
        let bar = "bar";

        assert_eq!(Substr::make(foobar1, foo)?.recover(foobar2)?, "foo");
        assert_eq!(Substr::make(foobar1, bar)?.recover(foobar2)?, "bar");
        Ok(())
    }

    #[test]
    fn equality() -> Result<(), ()> {
        let foobar = "foobar";
        let (foo, bar) = foobar.split_at(3);
        let empty = foobar.split_at(0).0;

        let foo_sub = Substr::make(foobar, foo)?;
        let bar_sub = Substr::make(foobar, bar)?;
        let empty_sub = Substr::make(foobar, empty)?;

        assert_eq!(foo_sub, foo_sub);
        assert_ne!(foo_sub, bar_sub);
        assert_ne!(foo_sub, empty_sub);

        assert_ne!(bar_sub, foo_sub);
        assert_eq!(bar_sub, bar_sub);
        assert_ne!(bar_sub, empty_sub);

        assert_ne!(empty_sub, foo_sub);
        assert_ne!(empty_sub, bar_sub);
        assert_eq!(empty_sub, empty_sub);

        Ok(())
    }

    #[test]
    fn equality_with_different_parents() -> Result<(), ()> {
        let foo1bar1 = "foo1bar1";
        let (foo1, bar1) = foo1bar1.split_at(4);

        let foo2bar2 = "foo2bar2";
        let (foo2, bar2) = foo2bar2.split_at(4);

        let foo1_sub = Substr::make(foo1bar1, foo1)?;
        let foo2_sub = Substr::make(foo2bar2, foo2)?;
        let bar1_sub = Substr::make(foo1bar1, bar1)?;
        let bar2_sub = Substr::make(foo2bar2, bar2)?;

        assert_eq!(foo1_sub, foo2_sub);
        assert_eq!(bar1_sub, bar2_sub);
        Ok(())
    }

    #[test]
    fn find_substr() -> Result<(), ()> {
        let foobar = "foobar";
        let foo = "foo";
        let bar = "bar";

        assert_eq!(foobar.find_substr(foo).ok_or(())?.recover(foobar)?, "foo");
        assert_eq!(foobar.find_substr(bar).ok_or(())?.recover(foobar)?, "bar");
        Ok(())
    }

    #[test]
    fn to_range() -> Result<(), ()> {
        let foobar = "foobar";
        let (foo, bar) = foobar.split_at(3);

        
        let foo_sub = Substr::make(foobar, foo)?;
        let bar_sub = Substr::make(foobar, bar)?;

        let foo_range: Range<usize> = foo_sub.into();
        let bar_range: Range<usize> = bar_sub.into();

        assert_eq!(foo_range.start, 0);
        assert_eq!(foo_range.end, 3);
        assert_eq!(bar_range.start, 3);
        assert_eq!(bar_range.end, 6);
        Ok(())
    }

    #[test]
    fn from_range() -> Result<(), ()> {
        let foo_range = Range::<usize> {
            start: 0,
            end: 3,
        };
        let bar_range = Range::<usize> {
            start: 3,
            end: 6,
        };

        
        let foo_sub: Substr = foo_range.into();
        let bar_sub: Substr = bar_range.into();

        let foobar = "foobar";
        let foo = foo_sub.recover(foobar)?;
        let bar = bar_sub.recover(foobar)?;

        assert_eq!(foo, "foo");
        assert_eq!(bar, "bar");
        Ok(())
    }
}
