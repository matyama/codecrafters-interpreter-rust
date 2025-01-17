use std::fmt::Display;

#[derive(Clone, Debug)]
pub struct Value(pub f64);

impl Display for Value {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{value}", value = self.0)
    }
}
