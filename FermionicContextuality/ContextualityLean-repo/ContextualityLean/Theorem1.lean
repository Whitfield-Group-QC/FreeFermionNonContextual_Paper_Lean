import ContextualityLean.Graph
import ContextualityLean.Pauli

/-!
# Theorem 1: Non-contextual Pauli Hamiltonians are twin-free-fermion-disguised

A Hamiltonian is modelled by its terms `t : ι → PauliVec n` (coefficients play no role in
either statement). Reading (a) of "twin-free-fermion-disguised" is used: after projecting out
twin vertices, the frustration graph is a line graph.

* `theorem1_inclusion` : non-contextual ⇒ twin-free-fermion-disguised.
* `theorem1_strict`    : the converse fails, witnessed by `H_S^1` of Eq. (12), which has four
                         pairwise-anticommuting terms.
-/

namespace FermionicNC

open Function

universe u

variable {ι : Type u} {n : ℕ}

/-- Paper, Definition (Frustration Graph): vertices are terms, edges join anticommuting terms. -/
def frustrationGraph (t : ι → PauliVec n) : SimpleGraph ι where
  Adj i j := symp (t i) (t j) = 1
  symm := ⟨by
    intro i j h
    change symp (t j) (t i) = 1
    rw [symp_comm]
    exact h⟩
  loopless := ⟨by
    intro i h
    have h' : symp (t i) (t i) = 1 := h
    rw [symp_self] at h'
    exact absurd h' (by decide)⟩

instance (t : ι → PauliVec n) : DecidableRel (frustrationGraph t).Adj :=
  fun i j => inferInstanceAs (Decidable (symp (t i) (t j) = 1))

/-- Term `i` lies in `S' = S \ G`: it anticommutes with some term. -/
def InSPrime (t : ι → PauliVec n) (i : ι) : Prop := ∃ j, symp (t i) (t j) = 1

/-- Paper, Definition 1: commutation is an equivalence relation on `S'` (reflexivity and
symmetry are automatic, so this is transitivity). -/
def IsNoncontextual (t : ι → PauliVec n) : Prop :=
  ∀ a b c, InSPrime t a → InSPrime t b → InSPrime t c →
    symp (t a) (t b) = 0 → symp (t b) (t c) = 0 → symp (t a) (t c) = 0

/-- Reading (a): every twin reduction of the frustration graph is a line graph. -/
def IsTwinFFDisguised (t : ι → PauliVec n) : Prop :=
  ∀ R : Set ι, IsTwinTransversal (frustrationGraph t) R →
    IsLineGraph ((frustrationGraph t).induce R)

theorem IsNoncontextual.isNCGraph {t : ι → PauliVec n} (h : IsNoncontextual t) :
    IsNCGraph (frustrationGraph t) := by
  intro x y z hx hy hz hxy hyz hxz
  have sprime : ∀ i, ¬ IsIsolated (frustrationGraph t) i → InSPrime t i := by
    intro i hi
    by_contra hc
    exact hi (fun w hw => hc ⟨w, hw⟩)
  have e₁ : symp (t x) (t y) = 0 := (zmod2_eq_zero_iff_ne_one _).2 hxy
  have e₂ : symp (t y) (t z) = 0 := (zmod2_eq_zero_iff_ne_one _).2 hyz
  have e₃ := h x y z (sprime x hx) (sprime y hy) (sprime z hz) e₁ e₂
  exact (zmod2_eq_zero_iff_ne_one _).1 e₃ hxz

/-- **Theorem 1, inclusion.** -/
theorem theorem1_inclusion {t : ι → PauliVec n} (h : IsNoncontextual t) :
    IsTwinFFDisguised t :=
  fun _ hR => h.isNCGraph.twinReduction_isLineGraph hR

/-! ## Strictness witness: `H_S^1` from Eq. (12) -/

/-- `H_S^1 = Z₂ + Z₁X₂X₃ + Y₁X₂X₄ + Y₁Z₂X₄ + X₁Z₃Z₄ + Z₁X₂Z₃`. -/
def H_S1 : Fin 6 → PauliVec 4 :=
  ![pauliOf ![P1.I, P1.Z, P1.I, P1.I],
    pauliOf ![P1.Z, P1.X, P1.X, P1.I],
    pauliOf ![P1.Y, P1.X, P1.I, P1.X],
    pauliOf ![P1.Y, P1.Z, P1.I, P1.X],
    pauliOf ![P1.X, P1.I, P1.Z, P1.Z],
    pauliOf ![P1.Z, P1.X, P1.Z, P1.I]]

/-- Root graph: a 4-leaf star (centre `0`, leaves `1,2,3,4` for terms 0,1,2,5), plus pendant
edges `{3,5}` (term 3) and `{4,6}` (term 4). -/
def rootS1 : Fin 6 → Sym2 (Fin 7) :=
  ![s(0, 1), s(0, 2), s(0, 3), s(3, 5), s(4, 6), s(0, 4)]

theorem H_S1_isLineGraph : IsLineGraph (frustrationGraph H_S1) :=
  ⟨Fin 7, rootS1, by decide, by decide, by decide⟩

/-- Transitivity of commutation fails at `(0, 3, 1)`:
`[t₀,t₃] = 0`, `[t₃,t₁] = 0`, but `{t₀,t₁} = 0`. -/
theorem H_S1_contextual : ¬ IsNoncontextual H_S1 := by
  intro h
  have := h 0 3 1 ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide) (by decide)
  exact absurd this (by decide)

/-- **Theorem 1, strictness.** A twin-free-fermion-disguised Hamiltonian with four pairwise
anticommuting terms that is not non-contextual. -/
theorem theorem1_strict :
    ∃ t : Fin 6 → PauliVec 4, Injective t ∧ IsTwinFFDisguised t ∧ ¬ IsNoncontextual t ∧
      ∃ k : Fin 4 → Fin 6, Injective k ∧ ∀ i j, i ≠ j → symp (t (k i)) (t (k j)) = 1 :=
  ⟨H_S1, by decide, fun R _ => H_S1_isLineGraph.induce R, H_S1_contextual,
    ![0, 1, 2, 5], by decide, by decide⟩

end FermionicNC
