#!/usr/bin/env python3
"""Compile engineered color-template search hosts into quotient diagnostics.

Input is a JSON spec with:

  {
    "name": "K4 equal fibers",
    "template": {
      "vertices": ["r", "g", "b", "y"],
      "edges": [["r", "g"], ["r", "b"], ...]
    },
    "fibers": {"r": 8, "g": 8, "b": 8, "y": 8},
    "marked": {"r": 1},
    "scan": {"steps": 1200}
  }

The host graph is the complete weighted join of the fibers, programmed by the
template. The quotient matrices are exact for cell-uniform states.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


TOL = 1e-8


@dataclass(frozen=True)
class Spec:
    name: str
    problem: dict[str, Any]
    vertices: list[str]
    weights: np.ndarray
    fibers: np.ndarray
    marked: np.ndarray
    scan_steps: int
    t_max_factor: float
    gamma_factors: list[float]
    gamma_adjacency: float | None
    gamma_laplacian: float | None


def parse_spec(path: Path) -> Spec:
    raw = json.loads(path.read_text())
    vertices, weights = build_template(raw["template"])

    fibers_raw = raw.get("fibers", raw.get("fiber_size"))
    if isinstance(fibers_raw, int):
        fibers = np.array([fibers_raw] * len(vertices), dtype=int)
    else:
        fibers = np.array([int(fibers_raw[v]) for v in vertices], dtype=int)
    if np.any(fibers <= 0):
        raise ValueError("all fiber sizes must be positive")

    marked_raw = raw.get("marked", {})
    marked = np.array([int(marked_raw.get(v, 0)) for v in vertices], dtype=int)
    if np.any(marked < 0) or np.any(marked > fibers):
        raise ValueError("marked counts must satisfy 0 <= marked[v] <= fibers[v]")

    scan = raw.get("scan", {})
    return Spec(
        name=str(raw.get("name", path.stem)),
        problem=dict(raw.get("problem", {})),
        vertices=vertices,
        weights=weights,
        fibers=fibers,
        marked=marked,
        scan_steps=int(scan.get("steps", 1600)),
        t_max_factor=float(scan.get("t_max_factor", 4.0)),
        gamma_factors=[float(x) for x in scan.get(
            "gamma_factors", [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
        )],
        gamma_adjacency=_optional_float(scan.get("gamma_adjacency")),
        gamma_laplacian=_optional_float(scan.get("gamma_laplacian")),
    )


def build_template(template: dict[str, Any]) -> tuple[list[str], np.ndarray]:
    """Build a weighted template graph from an explicit spec or constructor."""
    kind = template.get("kind", "explicit")
    if kind == "explicit":
        vertices = [str(v) for v in template["vertices"]]
        weights = empty_weights(len(vertices))
        add_edges(weights, vertices, template.get("edges", []))
        return vertices, weights
    if kind == "complete":
        vertices = named_vertices(template)
        weights = np.ones((len(vertices), len(vertices)), dtype=float)
        np.fill_diagonal(weights, 0.0)
        return vertices, weights * float(template.get("weight", 1.0))
    if kind == "cycle":
        vertices = named_vertices(template)
        weights = empty_weights(len(vertices))
        n = len(vertices)
        for i in range(n):
            add_edge(weights, i, (i + 1) % n, float(template.get("weight", 1.0)))
        return vertices, weights
    if kind == "cycle_power_law":
        vertices = named_vertices(template)
        n = len(vertices)
        alpha = float(template["alpha"])
        scale = float(template.get("scale", 1.0))
        weights = empty_weights(n)
        for i in range(n):
            for j in range(i + 1, n):
                dist = min((j - i) % n, (i - j) % n)
                add_edge(weights, i, j, scale / (dist**alpha))
        return vertices, weights
    if kind == "path":
        vertices = named_vertices(template)
        weights = empty_weights(len(vertices))
        for i in range(len(vertices) - 1):
            add_edge(weights, i, i + 1, float(template.get("weight", 1.0)))
        return vertices, weights
    if kind == "complete_bipartite":
        left = [str(v) for v in template.get("left", [])]
        right = [str(v) for v in template.get("right", [])]
        if not left:
            left = [f"L{i}" for i in range(int(template["n_left"]))]
        if not right:
            right = [f"R{i}" for i in range(int(template["n_right"]))]
        vertices = left + right
        weights = empty_weights(len(vertices))
        weight = float(template.get("weight", 1.0))
        for i in range(len(left)):
            for j in range(len(left), len(vertices)):
                add_edge(weights, i, j, weight)
        return vertices, weights
    if kind == "hypercube":
        dim = int(template["dim"])
        vertices = [format(i, f"0{dim}b") for i in range(2**dim)]
        weights = empty_weights(len(vertices))
        weight = float(template.get("weight", 1.0))
        for i in range(2**dim):
            for bit in range(dim):
                j = i ^ (1 << bit)
                if i < j:
                    add_edge(weights, i, j, weight)
        return vertices, weights
    if kind == "surface_heawood":
        colors = heawood_number(template)
        vertices = [f"c{i}" for i in range(colors)]
        weights = np.ones((colors, colors), dtype=float)
        np.fill_diagonal(weights, 0.0)
        return vertices, weights * float(template.get("weight", 1.0))
    if kind == "cartesian_product":
        left_vertices, left_weights = build_template(template["left"])
        right_vertices, right_weights = build_template(template["right"])
        vertices = [f"{a},{b}" for a in left_vertices for b in right_vertices]
        weights = empty_weights(len(vertices))
        right_n = len(right_vertices)
        for ai in range(len(left_vertices)):
            for aj in range(len(left_vertices)):
                if left_weights[ai, aj] != 0:
                    for b in range(right_n):
                        add_edge(weights, ai * right_n + b, aj * right_n + b, left_weights[ai, aj])
        for a in range(len(left_vertices)):
            for bi in range(right_n):
                for bj in range(right_n):
                    if right_weights[bi, bj] != 0:
                        add_edge(weights, a * right_n + bi, a * right_n + bj, right_weights[bi, bj])
        return vertices, weights
    if kind == "complement":
        vertices, base = build_template(template["of"])
        weight = float(template.get("weight", 1.0))
        weights = np.where(np.eye(len(vertices), dtype=bool), 0.0, np.where(base == 0, weight, 0.0))
        return vertices, weights
    raise ValueError(f"unknown template kind: {kind!r}")


def heawood_number(template: dict[str, Any]) -> int:
    """Return the standard surface color upper bound as a complete template size."""
    if "colors" in template:
        return int(template["colors"])
    if "orientable_genus" in template:
        g = int(template["orientable_genus"])
        if g < 0:
            raise ValueError("orientable_genus must be nonnegative")
        return int(math.floor((7.0 + math.sqrt(1.0 + 48.0 * g)) / 2.0))
    if "nonorientable_genus" in template:
        k = int(template["nonorientable_genus"])
        if k < 1:
            raise ValueError("nonorientable_genus must be positive")
        if k == 2 and bool(template.get("klein_bottle_exception", True)):
            return 6
        return int(math.floor((7.0 + math.sqrt(1.0 + 24.0 * k)) / 2.0))
    if "euler_genus" in template:
        eps = int(template["euler_genus"])
        if eps < 0:
            raise ValueError("euler_genus must be nonnegative")
        if eps == 0:
            return 4
        if eps == 2 and bool(template.get("klein_bottle_exception", False)):
            return 6
        return int(math.floor((7.0 + math.sqrt(1.0 + 24.0 * eps)) / 2.0))
    raise ValueError("surface_heawood needs orientable_genus, nonorientable_genus, euler_genus, or colors")


def named_vertices(template: dict[str, Any]) -> list[str]:
    if "vertices" in template:
        return [str(v) for v in template["vertices"]]
    n = int(template["n"])
    prefix = str(template.get("prefix", "v"))
    return [f"{prefix}{i}" for i in range(n)]


def empty_weights(n: int) -> np.ndarray:
    return np.zeros((n, n), dtype=float)


def add_edges(weights: np.ndarray, vertices: list[str], edges: list[Any]) -> None:
    index = {v: i for i, v in enumerate(vertices)}
    for edge in edges:
        if len(edge) == 2:
            u, v = edge
            w = 1.0
        elif len(edge) == 3:
            u, v, w = edge
            w = float(w)
        else:
            raise ValueError(f"edge must have length 2 or 3: {edge!r}")
        add_edge(weights, index[str(u)], index[str(v)], w)


def add_edge(weights: np.ndarray, i: int, j: int, weight: float) -> None:
    if i == j:
        raise ValueError("template self-loops are not supported")
    weights[i, j] = weights[j, i] = weight


def _optional_float(value: Any) -> float | None:
    if value is None or value == "auto":
        return None
    return float(value)


def weighted_degrees(weights: np.ndarray, sizes: np.ndarray | None = None) -> np.ndarray:
    if sizes is None:
        return weights.sum(axis=1)
    return weights @ sizes.astype(float)


def adjacency_quotient(weights: np.ndarray, sizes: np.ndarray) -> np.ndarray:
    roots = np.sqrt(sizes.astype(float))
    return weights * np.outer(roots, roots)


def laplacian_quotient(weights: np.ndarray, sizes: np.ndarray) -> np.ndarray:
    aq = adjacency_quotient(weights, sizes)
    deg = weighted_degrees(weights, sizes)
    return np.diag(deg) - aq


def full_laplacian_spectrum(weights: np.ndarray, sizes: np.ndarray) -> np.ndarray:
    lq = laplacian_quotient(weights, sizes)
    vals = list(np.linalg.eigvalsh(lq))
    deg = weighted_degrees(weights, sizes)
    for d, n in zip(deg, sizes, strict=True):
        vals.extend([float(d)] * int(n - 1))
    return np.array(sorted(vals))


def marked_cells(spec: Spec) -> tuple[list[str], np.ndarray, np.ndarray]:
    labels: list[str] = []
    source: list[int] = []
    sizes: list[int] = []
    for i, v in enumerate(spec.vertices):
        m = int(spec.marked[i])
        u = int(spec.fibers[i] - m)
        if m > 0:
            labels.append(f"{v}:M")
            source.append(i)
            sizes.append(m)
        if u > 0:
            labels.append(f"{v}:U")
            source.append(i)
            sizes.append(u)
    return labels, np.array(source, dtype=int), np.array(sizes, dtype=int)


def refined_weights(weights: np.ndarray, source: np.ndarray) -> np.ndarray:
    k = len(source)
    out = np.zeros((k, k), dtype=float)
    for a in range(k):
        for b in range(k):
            if source[a] != source[b]:
                out[a, b] = weights[source[a], source[b]]
    return out


def projector_marked(labels: list[str]) -> np.ndarray:
    return np.diag([1.0 if label.endswith(":M") else 0.0 for label in labels])


def spectral_ratio_if_regular(weights: np.ndarray) -> tuple[bool, float | None, np.ndarray]:
    deg = weighted_degrees(weights)
    regular = bool(np.allclose(deg, deg[0], atol=TOL))
    if not regular or abs(deg[0]) <= TOL:
        return regular, None, deg
    vals = np.linalg.eigvalsh(weights)
    top = float(vals[-1])
    rest = vals[:-1]
    ratio = float(np.max(np.abs(rest)) / abs(top)) if len(rest) else 0.0
    return regular, ratio, deg


def is_integral_spectrum(vals: np.ndarray) -> bool:
    return bool(np.allclose(vals, np.round(vals), atol=1e-7))


def format_matrix(matrix: np.ndarray, labels: list[str]) -> str:
    width = max(9, *(len(x) for x in labels))
    header = " " * width + " " + " ".join(f"{x:>{width}}" for x in labels)
    rows = [header]
    for label, row in zip(labels, matrix, strict=True):
        cells = " ".join(f"{x:>{width}.4g}" for x in row)
        rows.append(f"{label:>{width}} {cells}")
    return "\n".join(rows)


def fmt_vals(vals: np.ndarray, max_items: int = 18) -> str:
    vals = np.array(vals, dtype=float)
    if len(vals) <= max_items:
        return ", ".join(f"{x:.6g}" for x in vals)
    head_count = max_items // 2
    tail_count = max_items - head_count
    head = ", ".join(f"{x:.6g}" for x in vals[:head_count])
    tail = ", ".join(f"{x:.6g}" for x in vals[-tail_count:])
    return f"{head}, ..., {tail}"


def scan_search(
    hamiltonian: np.ndarray,
    cell_sizes: np.ndarray,
    marked_diag: np.ndarray,
    t_max: float,
    steps: int,
) -> tuple[float, float]:
    if not np.any(np.diag(marked_diag) > 0.5):
        return 0.0, 0.0
    vals, vecs = np.linalg.eigh(hamiltonian)
    initial = np.sqrt(cell_sizes.astype(float) / float(np.sum(cell_sizes)))
    coeff = vecs.T.conj() @ initial
    marked_indices = np.where(np.diag(marked_diag) > 0.5)[0]
    best_t = 0.0
    best_p = -1.0
    for t in np.linspace(0.0, t_max, max(2, steps)):
        state = vecs @ (np.exp(-1j * vals * t) * coeff)
        p = float(np.sum(np.abs(state[marked_indices]) ** 2))
        if p > best_p:
            best_p = p
            best_t = float(t)
    return best_t, best_p


def choose_gamma_and_scan(
    base_gamma: float,
    fixed_gamma: float | None,
    gamma_factors: list[float],
    quotient: np.ndarray,
    projector: np.ndarray,
    cell_sizes: np.ndarray,
    t_max: float,
    steps: int,
) -> tuple[float, float, float]:
    candidates = [fixed_gamma] if fixed_gamma is not None else [base_gamma * f for f in gamma_factors]
    best_gamma = float(candidates[0])
    best_t = 0.0
    best_p = -1.0
    for gamma in candidates:
        hamiltonian = -float(gamma) * quotient - projector
        t, p = scan_search(hamiltonian, cell_sizes, projector, t_max, steps)
        if p > best_p:
            best_gamma = float(gamma)
            best_t = t
            best_p = p
    return best_gamma, best_t, best_p


def compile_report(spec: Spec) -> str:
    n_total = int(np.sum(spec.fibers))
    weighted_edges = 0.0
    for i in range(len(spec.vertices)):
        for j in range(i + 1, len(spec.vertices)):
            weighted_edges += spec.weights[i, j] * spec.fibers[i] * spec.fibers[j]

    aq = adjacency_quotient(spec.weights, spec.fibers)
    lq = laplacian_quotient(spec.weights, spec.fibers)
    template_adj_vals = np.linalg.eigvalsh(spec.weights)
    template_lap = np.diag(weighted_degrees(spec.weights)) - spec.weights
    template_lap_vals = np.linalg.eigvalsh(template_lap)
    quotient_adj_vals = np.linalg.eigvalsh(aq)
    quotient_lap_vals = np.linalg.eigvalsh(lq)
    full_lap_vals = full_laplacian_spectrum(spec.weights, spec.fibers)

    template_regular, template_ratio, template_deg = spectral_ratio_if_regular(spec.weights)
    host_deg = weighted_degrees(spec.weights, spec.fibers)
    host_regular = bool(np.allclose(host_deg, host_deg[0], atol=TOL))
    host_ratio = None
    if host_regular and abs(quotient_adj_vals[-1]) > TOL:
        host_ratio = float(np.max(np.abs(quotient_adj_vals[:-1])) / abs(quotient_adj_vals[-1]))

    cell_labels, source, cell_sizes = marked_cells(spec)
    rw = refined_weights(spec.weights, source)
    marked_aq = adjacency_quotient(rw, cell_sizes)
    marked_lq = laplacian_quotient(rw, cell_sizes)
    p_marked = projector_marked(cell_labels)
    t_max = spec.t_max_factor * math.sqrt(max(1, n_total))
    top_a = float(np.linalg.eigvalsh(marked_aq)[-1])
    base_gamma_a = 1.0 / top_a if abs(top_a) > TOL else 1.0
    top_l = float(np.linalg.eigvalsh(marked_lq)[-1])
    base_gamma_l = 1.0 / top_l if abs(top_l) > TOL else 1.0
    gamma_a, best_adj_t, best_adj_p = choose_gamma_and_scan(
        base_gamma_a,
        spec.gamma_adjacency,
        spec.gamma_factors,
        marked_aq,
        p_marked,
        cell_sizes,
        t_max,
        spec.scan_steps,
    )
    gamma_l, best_lap_t, best_lap_p = choose_gamma_and_scan(
        base_gamma_l,
        spec.gamma_laplacian,
        spec.gamma_factors,
        marked_lq,
        p_marked,
        cell_sizes,
        t_max,
        spec.scan_steps,
    )
    h_adj = -gamma_a * marked_aq - p_marked

    lines: list[str] = []
    lines.append(f"# Search Compiler Report: {spec.name}")
    lines.append("")
    if spec.problem:
        lines.append("## Problem")
        lines.append("")
        for key in ["domain", "task", "encoding", "compiler_goal", "proof_route"]:
            if key in spec.problem:
                lines.append(f"- {key.replace('_', ' ')}: {spec.problem[key]}")
        lines.append("")
    lines.append("## Host")
    lines.append("")
    lines.append(f"- template vertices: {len(spec.vertices)}")
    lines.append(f"- host vertices: {n_total}")
    lines.append(f"- weighted host edge mass: {weighted_edges:.6g}")
    lines.append(f"- fibers: {dict(zip(spec.vertices, map(int, spec.fibers), strict=True))}")
    lines.append(f"- marked counts: {dict(zip(spec.vertices, map(int, spec.marked), strict=True))}")
    lines.append("")
    lines.append("## Template Diagnostics")
    lines.append("")
    lines.append(f"- weighted degrees: {fmt_vals(template_deg)}")
    lines.append(f"- regular template: {template_regular}")
    lines.append(f"- template adjacency eigenvalues: {fmt_vals(template_adj_vals)}")
    if template_ratio is None:
        lines.append("- CNO spectral ratio: unavailable; template is not nontrivially regular")
    else:
        lines.append(f"- CNO spectral ratio max(|lambda_i|)/lambda_1: {template_ratio:.6g}")
        lines.append(f"- CNO ratio passes strict < 1 check: {template_ratio < 1.0 - 1e-7}")
    lines.append(f"- template Laplacian eigenvalues: {fmt_vals(template_lap_vals)}")
    lines.append(f"- template Laplacian integral: {is_integral_spectrum(template_lap_vals)}")
    lines.append("")
    lines.append("## Fiber Quotient")
    lines.append("")
    lines.append(f"- host weighted degrees by fiber: {fmt_vals(host_deg)}")
    lines.append(f"- regular host: {host_regular}")
    if host_ratio is not None:
        lines.append(f"- host quotient spectral ratio: {host_ratio:.6g}")
    lines.append(f"- quotient adjacency eigenvalues: {fmt_vals(quotient_adj_vals)}")
    lines.append(f"- quotient Laplacian eigenvalues: {fmt_vals(quotient_lap_vals)}")
    lines.append(f"- full host Laplacian integral: {is_integral_spectrum(full_lap_vals)}")
    lines.append(f"- full host Laplacian eigenvalues: {fmt_vals(full_lap_vals)}")
    lines.append("")
    lines.append("Adjacency quotient on uniform fiber states:")
    lines.append("")
    lines.append("```text")
    lines.append(format_matrix(aq, spec.vertices))
    lines.append("```")
    lines.append("")
    lines.append("## Marked Quotient")
    lines.append("")
    lines.append(f"- cells: {dict(zip(cell_labels, map(int, cell_sizes), strict=True))}")
    lines.append(f"- gamma factors searched: {spec.gamma_factors if spec.gamma_adjacency is None or spec.gamma_laplacian is None else 'fixed'}")
    lines.append(f"- adjacency gamma: {gamma_a:.8g}")
    lines.append(f"- laplacian gamma: {gamma_l:.8g}")
    lines.append(f"- scan horizon: [0, {t_max:.6g}] with {spec.scan_steps} steps")
    lines.append(f"- best adjacency-CTQW marked probability: {best_adj_p:.6g} at t={best_adj_t:.6g}")
    lines.append(f"- best laplacian-CTQW marked probability: {best_lap_p:.6g} at t={best_lap_t:.6g}")
    lines.append("")
    lines.append("Marked-cell adjacency quotient:")
    lines.append("")
    lines.append("```text")
    lines.append(format_matrix(marked_aq, cell_labels))
    lines.append("```")
    lines.append("")
    lines.append("Marked-cell adjacency search Hamiltonian:")
    lines.append("")
    lines.append("```text")
    lines.append(format_matrix(h_adj, cell_labels))
    lines.append("```")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path, help="JSON compiler spec")
    parser.add_argument("--report", type=Path, help="write Markdown report to this path")
    args = parser.parse_args()

    spec = parse_spec(args.spec)
    report = compile_report(spec)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(report + "\n")
    print(report)


if __name__ == "__main__":
    main()
