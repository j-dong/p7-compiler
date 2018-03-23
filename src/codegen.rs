use std::io::prelude::*;

pub struct CodeGenerator<'a, W: Write + 'a> {
    out: &'a W,
}
