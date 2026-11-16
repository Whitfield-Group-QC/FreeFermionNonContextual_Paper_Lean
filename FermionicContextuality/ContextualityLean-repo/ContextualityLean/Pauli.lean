import Mathlib

/-!
# Phase-free Pauli strings in binary symplectic form

Shared by Theorems 1 and 2. Theorem 1 only needs (anti)commutation, which is phase-independent.
Phases are added in the Theorem 2 layer.
-/

namespace FermionicNC

/-- Phase-free `n`-qubit Pauli string as `(x | z)` bit vectors:
`I = (0,0)`, `X = (1,0)`, `Y = (1,1)`, `Z = (0,1)` on each qubit. -/
abbrev PauliVec (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- Binary symplectic form: two Pauli strings commute iff `symp = 0` and anticommute iff
`symp = 1`. (This correspondence with matrix (anti)commutation is the standard fact taken as
the modelling assumption; see README.) -/
def symp {n : ℕ} (p q : PauliVec n) : ZMod 2 :=
  ∑ i, (p.1 i * q.2 i + p.2 i * q.1 i)

theorem symp_comm {n : ℕ} (p q : PauliVec n) : symp p q = symp q p := by
  unfold symp
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem symp_self {n : ℕ} (p : PauliVec n) : symp p p = 0 := by
  unfold symp
  apply Finset.sum_eq_zero
  intro i _
  have key : ∀ a b : ZMod 2, a * b + b * a = 0 := by decide
  exact key _ _

theorem zmod2_eq_zero_iff_ne_one : ∀ a : ZMod 2, a = 0 ↔ a ≠ 1 := by decide

/-- Single-qubit Pauli labels, for writing explicit Hamiltonians. -/
inductive P1
  | I
  | X
  | Y
  | Z
  deriving DecidableEq

def P1.xbit : P1 → ZMod 2
  | .I => 0
  | .X => 1
  | .Y => 1
  | .Z => 0

def P1.zbit : P1 → ZMod 2
  | .I => 0
  | .X => 0
  | .Y => 1
  | .Z => 1

/-- `pauliOf ![P1.Z, P1.X, P1.X, P1.I]` is the string `Z₁X₂X₃`. -/
def pauliOf {n : ℕ} (s : Fin n → P1) : PauliVec n :=
  (fun i => (s i).xbit, fun i => (s i).zbit)

end FermionicNC
