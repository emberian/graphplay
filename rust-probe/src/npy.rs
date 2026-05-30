//! Minimal `.npy` reader/writer for 2-D `f64`/`f32` C-contiguous arrays, plus a
//! trivial raw binary format (`<u64 rows><u64 cols><f64 data...>`, little-endian)
//! and CSV. We only support what the probe needs: dense real n×n matrices.

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use ndarray::Array2;
use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::Path;

/// Errors from matrix I/O.
#[derive(Debug)]
pub enum IoError {
    Io(io::Error),
    Format(String),
}

impl std::fmt::Display for IoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IoError::Io(e) => write!(f, "io error: {e}"),
            IoError::Format(s) => write!(f, "format error: {s}"),
        }
    }
}
impl std::error::Error for IoError {}
impl From<io::Error> for IoError {
    fn from(e: io::Error) -> Self {
        IoError::Io(e)
    }
}

/// Load a 2-D real matrix from a file, dispatching on extension:
/// `.npy` (numpy), `.csv`, or `.bin` (our raw format). Unknown extensions try npy.
pub fn load_matrix<P: AsRef<Path>>(path: P) -> Result<Array2<f64>, IoError> {
    let p = path.as_ref();
    match p.extension().and_then(|e| e.to_str()) {
        Some("csv") => load_csv(p),
        Some("bin") => load_raw(p),
        _ => load_npy(p),
    }
}

/// Parse the `.npy` v1.0/v2.0 header + a 2-D C-contiguous `<f4`/`<f8` payload.
pub fn load_npy<P: AsRef<Path>>(path: P) -> Result<Array2<f64>, IoError> {
    let mut f = BufReader::new(File::open(path)?);
    let mut magic = [0u8; 6];
    f.read_exact(&mut magic)?;
    if &magic != b"\x93NUMPY" {
        return Err(IoError::Format("not a .npy file (bad magic)".into()));
    }
    let major = f.read_u8()?;
    let _minor = f.read_u8()?;
    let header_len = if major >= 2 {
        f.read_u32::<LittleEndian>()? as usize
    } else {
        f.read_u16::<LittleEndian>()? as usize
    };
    let mut header_bytes = vec![0u8; header_len];
    f.read_exact(&mut header_bytes)?;
    let header = String::from_utf8(header_bytes)
        .map_err(|_| IoError::Format("non-utf8 npy header".into()))?;

    let descr = extract_field(&header, "descr")
        .ok_or_else(|| IoError::Format("missing descr".into()))?;
    let fortran = extract_field(&header, "fortran_order")
        .map(|s| s.contains("True"))
        .unwrap_or(false);
    if fortran {
        return Err(IoError::Format(
            "fortran_order=True not supported (re-save C-contiguous)".into(),
        ));
    }
    let shape = extract_shape(&header)
        .ok_or_else(|| IoError::Format("missing/ malformed shape".into()))?;
    if shape.len() != 2 {
        return Err(IoError::Format(format!(
            "expected 2-D array, got {}-D",
            shape.len()
        )));
    }
    let (rows, cols) = (shape[0], shape[1]);
    let n = rows * cols;

    let data: Vec<f64> = if descr.contains("f8") {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(f.read_f64::<LittleEndian>()?);
        }
        v
    } else if descr.contains("f4") {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(f.read_f32::<LittleEndian>()? as f64);
        }
        v
    } else {
        return Err(IoError::Format(format!(
            "unsupported dtype {descr}; need <f4 or <f8"
        )));
    };

    Array2::from_shape_vec((rows, cols), data)
        .map_err(|e| IoError::Format(format!("shape mismatch: {e}")))
}

/// Save a matrix as a `.npy` v1.0 `<f8` C-contiguous array.
pub fn save_npy<P: AsRef<Path>>(path: P, a: &Array2<f64>) -> Result<(), IoError> {
    let mut f = BufWriter::new(File::create(path)?);
    let (rows, cols) = a.dim();
    let dict = format!(
        "{{'descr': '<f8', 'fortran_order': False, 'shape': ({rows}, {cols}), }}"
    );
    // total header (magic 6 + ver 2 + len 2 + dict) padded to multiple of 64.
    let unpadded = 10 + dict.len() + 1; // +1 for trailing '\n'
    let pad = (64 - (unpadded % 64)) % 64;
    let mut header = dict.into_bytes();
    header.extend(std::iter::repeat_n(b' ', pad));
    header.push(b'\n');
    f.write_all(b"\x93NUMPY")?;
    f.write_u8(1)?;
    f.write_u8(0)?;
    f.write_u16::<LittleEndian>(header.len() as u16)?;
    f.write_all(&header)?;
    for &x in a.iter() {
        f.write_f64::<LittleEndian>(x)?;
    }
    Ok(())
}

/// Raw binary: `<u64 rows><u64 cols><f64 data row-major...>`, little-endian.
pub fn load_raw<P: AsRef<Path>>(path: P) -> Result<Array2<f64>, IoError> {
    let mut f = BufReader::new(File::open(path)?);
    let rows = f.read_u64::<LittleEndian>()? as usize;
    let cols = f.read_u64::<LittleEndian>()? as usize;
    let n = rows * cols;
    let mut data = Vec::with_capacity(n);
    for _ in 0..n {
        data.push(f.read_f64::<LittleEndian>()?);
    }
    Array2::from_shape_vec((rows, cols), data)
        .map_err(|e| IoError::Format(format!("shape mismatch: {e}")))
}

/// Raw binary writer (matching [`load_raw`]).
pub fn save_raw<P: AsRef<Path>>(path: P, a: &Array2<f64>) -> Result<(), IoError> {
    let mut f = BufWriter::new(File::create(path)?);
    let (rows, cols) = a.dim();
    f.write_u64::<LittleEndian>(rows as u64)?;
    f.write_u64::<LittleEndian>(cols as u64)?;
    for &x in a.iter() {
        f.write_f64::<LittleEndian>(x)?;
    }
    Ok(())
}

/// CSV: comma- or whitespace-separated rows of floats.
pub fn load_csv<P: AsRef<Path>>(path: P) -> Result<Array2<f64>, IoError> {
    let mut s = String::new();
    File::open(path)?.read_to_string(&mut s)?;
    let mut rows: Vec<Vec<f64>> = Vec::new();
    for line in s.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let row: Result<Vec<f64>, _> = line
            .split([',', ' ', '\t'])
            .filter(|t| !t.is_empty())
            .map(|t| t.parse::<f64>())
            .collect();
        rows.push(row.map_err(|e| IoError::Format(format!("bad csv float: {e}")))?);
    }
    if rows.is_empty() {
        return Err(IoError::Format("empty csv".into()));
    }
    let cols = rows[0].len();
    if rows.iter().any(|r| r.len() != cols) {
        return Err(IoError::Format("ragged csv rows".into()));
    }
    let flat: Vec<f64> = rows.into_iter().flatten().collect();
    let nrows = flat.len() / cols;
    Array2::from_shape_vec((nrows, cols), flat)
        .map_err(|e| IoError::Format(format!("shape mismatch: {e}")))
}

fn extract_field<'a>(header: &'a str, key: &str) -> Option<&'a str> {
    // looks for `'key': <value>` and returns the value token up to the next comma
    let needle = format!("'{key}':");
    let start = header.find(&needle)? + needle.len();
    let rest = &header[start..];
    let end = rest.find(',').unwrap_or(rest.len());
    Some(rest[..end].trim())
}

fn extract_shape(header: &str) -> Option<Vec<usize>> {
    let start = header.find("'shape':")? + "'shape':".len();
    let rest = &header[start..];
    let open = rest.find('(')?;
    let close = rest.find(')')?;
    let inner = &rest[open + 1..close];
    let dims: Vec<usize> = inner
        .split(',')
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .filter_map(|t| t.parse::<usize>().ok())
        .collect();
    Some(dims)
}
