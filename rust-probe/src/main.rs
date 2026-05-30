//! CLI for the equitable-partition + residual probe.
//!
//! Usage:
//!   rust-probe <matrix.npy|.csv|.bin> [--r-sweep q1,q2,...] [--k K]
//!              [--oversample O] [--n-iter I] [--eps E] [--out out.json]
//!
//!   rust-probe gen-block  <out.npy> --n N --blocks B [--noise S]
//!   rust-probe gen-random <out.npy> --n N [--seed S]
//!
//! The `--r-sweep` values are *quantization resolutions* (coarse→fine ⇒ few→many
//! cells); see `decompose.rs`. Results are written as JSON to `--out` (default stdout).

use rust_probe::decompose::{decompose, ProbeConfig};
use rust_probe::npy::{load_matrix, save_npy};
use ndarray::Array2;
use std::process::exit;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        usage();
        exit(2);
    }
    let cmd = args[1].as_str();
    let res = match cmd {
        "gen-block" => gen_block(&args[2..]),
        "gen-random" => gen_random(&args[2..]),
        "-h" | "--help" => {
            usage();
            Ok(())
        }
        _ => run_probe(&args[1..]),
    };
    if let Err(e) = res {
        eprintln!("error: {e}");
        exit(1);
    }
}

fn usage() {
    eprintln!(
        "rust-probe — equitable-partition + residual decomposition\n\
         \n\
         PROBE:\n  rust-probe <matrix.npy|.csv|.bin> [--r-sweep q1,q2,...] [--k K]\n\
         \t[--oversample O] [--n-iter I] [--eps E] [--out FILE]\n\
         \n\
         GENERATE (for benchmarking):\n\
         \x20 rust-probe gen-block  <out.npy> --n N --blocks B [--noise S] [--seed S]\n\
         \x20 rust-probe gen-random <out.npy> --n N [--seed S]"
    );
}

/// pull `--flag value` out of args; returns Option<value>.
fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
}

fn run_probe(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    let path = &args[0];
    let t0 = Instant::now();
    let a = load_matrix(path)?;
    let load_ms = t0.elapsed().as_secs_f64() * 1e3;
    eprintln!("loaded {}×{} matrix in {:.1} ms", a.nrows(), a.ncols(), load_ms);

    // default sweep: a few quantization resolutions coarse→fine.
    let sweep: Vec<f64> = match flag(args, "--r-sweep") {
        Some(s) => s
            .split(',')
            .map(|t| t.trim().parse::<f64>())
            .collect::<Result<_, _>>()?,
        None => vec![1.0, 4.0, 16.0, 64.0, 256.0],
    };

    let mut cfg = ProbeConfig::default();
    if let Some(v) = flag(args, "--k") {
        cfg.k = v.parse()?;
    }
    if let Some(v) = flag(args, "--oversample") {
        cfg.oversample = v.parse()?;
    }
    if let Some(v) = flag(args, "--n-iter") {
        cfg.n_iter = v.parse()?;
    }
    if let Some(v) = flag(args, "--eps") {
        cfg.eps = v.parse()?;
    }

    let t1 = Instant::now();
    let decomp = decompose(&a, &sweep, &cfg);
    let probe_ms = t1.elapsed().as_secs_f64() * 1e3;
    eprintln!(
        "probe ({} sweep points) in {:.1} ms",
        decomp.sweep.len(),
        probe_ms
    );
    for sp in &decomp.sweep {
        eprintln!(
            "  quant={:>8.1}  r={:>6}  rel_defect={:.4}  resid_rank_eps={:>3}  σ1(R)={:.4}",
            sp.quant,
            sp.r,
            sp.rel_defect,
            sp.residual_rank_eps,
            sp.residual_svals.first().copied().unwrap_or(0.0)
        );
    }

    let json = serde_json::to_string_pretty(&decomp)?;
    match flag(args, "--out") {
        Some(out) => {
            std::fs::write(out, json)?;
            eprintln!("wrote results to {out}");
        }
        None => println!("{json}"),
    }
    Ok(())
}

// ---- generators (self-contained, deterministic) ----

struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed.wrapping_mul(0x2545F4914F6CDD1D) | 1)
    }
    fn next_f64(&mut self) -> f64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        ((x.wrapping_mul(0x2545F4914F6CDD1D) >> 11) as f64) / (1u64 << 53) as f64
    }
    fn normal(&mut self) -> f64 {
        let u1 = self.next_f64().max(1e-12);
        let u2 = self.next_f64();
        (-2.0 * u1.ln()).sqrt() * (std::f64::consts::TAU * u2).cos()
    }
}

fn gen_block(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    let out = &args[0];
    let n: usize = flag(args, "--n").ok_or("--n required")?.parse()?;
    let blocks: usize = flag(args, "--blocks").ok_or("--blocks required")?.parse()?;
    let noise: f64 = flag(args, "--noise").map(|s| s.parse()).transpose()?.unwrap_or(0.0);
    let seed: u64 = flag(args, "--seed").map(|s| s.parse()).transpose()?.unwrap_or(7);
    let mut rng = Lcg::new(seed);

    // random symmetric block values B (blocks×blocks)
    let mut bvals = vec![0.0f64; blocks * blocks];
    for c in 0..blocks {
        for cp in c..blocks {
            let v = rng.next_f64();
            bvals[c * blocks + cp] = v;
            bvals[cp * blocks + c] = v;
        }
    }
    let cell = |i: usize| (i * blocks) / n; // contiguous equal-ish blocks
    let mut a = Array2::<f64>::zeros((n, n));
    for i in 0..n {
        for j in 0..n {
            let base = bvals[cell(i) * blocks + cell(j)];
            a[[i, j]] = base + if noise > 0.0 { noise * rng.normal() } else { 0.0 };
        }
    }
    save_npy(out, &a)?;
    eprintln!("wrote {n}×{n} block matrix ({blocks} blocks, noise={noise}) to {out}");
    Ok(())
}

fn gen_random(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    let out = &args[0];
    let n: usize = flag(args, "--n").ok_or("--n required")?.parse()?;
    let seed: u64 = flag(args, "--seed").map(|s| s.parse()).transpose()?.unwrap_or(3);
    let mut rng = Lcg::new(seed);
    let mut a = Array2::<f64>::zeros((n, n));
    for v in a.iter_mut() {
        *v = rng.next_f64();
    }
    save_npy(out, &a)?;
    eprintln!("wrote {n}×{n} random matrix to {out}");
    Ok(())
}
