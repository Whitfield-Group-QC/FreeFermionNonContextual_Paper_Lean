# ContextualityLean

Lean 4 / Mathlib formalization of Theorems 1 and 2 of the accompanying paper on non-contextual
Pauli Hamiltonians and fermionic encodings.

Toolchain: `leanprover/lean4:v4.36.0-rc2` (see `lean-toolchain`); Mathlib version pinned in
`lake-manifest.json`.

## Building

```
lake exe cache get    # download precompiled Mathlib (otherwise Mathlib compiles from source: hours)
lake build
```

To confirm no step is assumed, add at the end of a file and rebuild:

```
#print axioms FermionicNC.theorem1_inclusion
#print axioms FermionicNC.theorem1_strict
#print axioms FermionicNC.theorem2_symplectic
```

Each should print only `[propext, Classical.choice, Quot.sound]` (Lean's standard axioms).

## Files

| File | Contents |
|---|---|
| `ContextualityLean/Graph.lean` | Twins, twin reduction, line graphs (induced subgraphs of the Johnson graph `J(n,2)`), graph form of non-contextuality, and the graph core of Theorem 1 |
| `ContextualityLean/Pauli.lean` | Phase-free Pauli strings in binary symplectic form `(x \| z)` |
| `ContextualityLean/Theorem1.lean` | Frustration graph, Definition 1, Theorem 1 and its strictness witness (`H_S^1`, Eq. 12) |
| `ContextualityLean/Symplectic.lean` | Symplectic linear algebra over 𝔽₂: anticommuting families, independence, projection, extension step |
| `ContextualityLean/Theorem2Core.lean` | Adapted-extension lemma and the encoding statement of Theorem 2 |

## Main results

| Paper | Lean |
|---|---|
| Theorem 1 (non-contextual ⇒ twin-free-fermion-disguised) | `theorem1_inclusion` |
| Theorem 1 (strict inclusion) | `theorem1_strict` |
| Existence of an extension adapted to the commuting generators | `exists_adapted_extension` |
| Theorem 2 (encoding) | `theorem2_symplectic` |

**Theorem 1.** "Twin-free-fermion-disguised" means: for every choice of one representative per
twin class, the induced frustration graph is a line graph. The strictness witness has six
distinct terms, four of them pairwise anticommuting, and is contextual.

**Theorem 2.** Specified Majorana operators are given as `l` pairs, plus optionally one unpaired
operator `x` (odd number of specified operators). For any commuting set `C` in their commutant,
the pairs extend to a full family of `2n` pairwise anticommuting Pauli strings, every element of
`C` lies in the span of the new pair sums, and so does `x + ∑ a` (the operator `Q`).

## Scope and assumptions

* Pauli strings are modelled as vectors in 𝔽₂²ⁿ; "anticommute" means symplectic form = 1.
  That this matches matrix (anti)commutation is standard but not proved here.
* Theorem 2 is verified up to phases, i.e. the encoding content. The rewrite of the Hamiltonian
  in Dirac operators (`-i γ γ = I - 2n`, `a_j`, `a_j†`) is not formalized.
* Hamiltonian coefficients play no role in either statement and are not modelled.
