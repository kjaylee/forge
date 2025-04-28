/// Information about a file or file range read operation
#[derive(Debug, Clone, PartialEq)]
pub struct FileInfo {
    /// Starting byte position of the read operation (adjusted for UTF-8
    /// boundaries)
    pub start_byte: u64,

    /// Ending byte position of the read operation (adjusted for UTF-8
    /// boundaries)
    pub end_byte: u64,

    /// Total file size
    pub total_size: u64,
}

impl FileInfo {
    /// Creates a new FileInfo with the specified parameters
    pub fn new(start_byte: u64, end_byte: u64, total_size: u64) -> Self {
        Self { start_byte, end_byte, total_size }
    }

    /// Returns true if this represents a partial file read
    pub fn is_partial(&self) -> bool {
        self.start_byte > 0 || self.end_byte < self.total_size
    }

    /// Returns the percentage of the file that was read (0.0 to 1.0)
    pub fn percent_read(&self) -> f64 {
        if self.total_size == 0 {
            return 0.0;
        }

        let bytes_read = self.end_byte - self.start_byte;
        bytes_read as f64 / self.total_size as f64
    }
}
