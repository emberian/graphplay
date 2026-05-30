//! # rust-probe
//!
//! High-throughput equitable-partition + residual decomposition core for the
//! attention-zoo probe (companion to `Graphplay/Integrations/AttentionComplexity.lean`
//! and `paper/explanatory_program.md` §2).
//!
//! Given a large real `n×n` matrix `A` (e.g. an attention head), it computes:
//!
//! 1. the **exact equitable partition** via 1-WL color refinement ([`wl`]);
//! 2. the **quotient** `B[c][c'] = mean block` and the **symmetric normalized
//!    quotient** `Q̃ = D^{1/2} Q D^{-1/2}` ([`quotient`]);
//! 3. the **residual** `R = A − A_eq` and its top-`k` singular values via
//!    randomized SVD ([`rsvd`]);
//! 4. a JSON-serializable [`decompose::Decomposition`] over a sweep ([`decompose`]).
//!
//! The semantics match the Lean spine: the lift is `A_eq[i][j] = B[cell i][cell j]`
//! (block-equitable), so a genuinely block-equitable `A` has zero residual.

pub mod decompose;
pub mod npy;
pub mod quotient;
pub mod rsvd;
pub mod wl;

pub use decompose::{decompose, decompose_at, Decomposition, ProbeConfig, SweepPoint};
pub use npy::{load_matrix, load_npy, save_npy};
pub use quotient::{lift, quotient, residual, symm_quotient, Quotient};
pub use wl::{equitable_defect, equitable_partition, Partition};
