#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub file: Option<String>,
    pub line: usize,
    pub column: usize,
}

impl SourceLocation {
    pub fn new(file: Option<String>) -> Self {
        Self {
            file: file,
            line: 1,
            column: 1,
        }
    }
}
