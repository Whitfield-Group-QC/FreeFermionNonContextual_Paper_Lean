import Mathlib

/-!
# Graph-theoretic core of Theorem 1

Definitions follow the paper:
* `IsTwin`            : Definition (Twin Vertices).
* `IsTwinTransversal` : "projecting out twin vertices" = keep one representative per twin class.
* `IsLineGraph`       : Definition (Johnson Graphs and Line Graphs), i.e. an induced subgraph of
                        `J(U,2)`: each vertex gets a 2-element subset (a non-diagonal `Sym2 U`),
                        injectively, and distinct vertices are adjacent iff their subsets meet.
* `IsNCGraph`         : graph form of Definition 1 (non-adjacency is transitive on
                        non-isolated vertices).

Main result: `IsNCGraph.twinReduction_isLineGraph`.
-/

namespace FermionicNC

open Function

universe u

/-! ## Twins -/

section Twins

variable {V : Type u} (G : SimpleGraph V)

/-- Paper, Definition (Twin Vertices). -/
def IsTwin (u v : V) : Prop := ∀ w, G.Adj u w ↔ G.Adj v w

variable {G}

theorem IsTwin.refl (v : V) : IsTwin G v v := fun _ => Iff.rfl

theorem IsTwin.symm {u v : V} (h : IsTwin G u v) : IsTwin G v u := fun w => (h w).symm

theorem IsTwin.trans {u v x : V} (h₁ : IsTwin G u v) (h₂ : IsTwin G v x) : IsTwin G u x :=
  fun w => (h₁ w).trans (h₂ w)

variable (G)

/-- Twinship is an equivalence relation. -/
def twinSetoid : Setoid V where
  r := IsTwin G
  iseqv := ⟨IsTwin.refl, IsTwin.symm, IsTwin.trans⟩

/-- "Projecting out twin vertices": `R` contains exactly one representative of each twin class. -/
structure IsTwinTransversal (R : Set V) : Prop where
  covers : ∀ v, ∃ r ∈ R, IsTwin G v r
  unique : ∀ r ∈ R, ∀ s ∈ R, IsTwin G r s → r = s

/-- Twin reductions exist, so statements quantified over all of them are not vacuous. -/
theorem exists_twinTransversal : ∃ R, IsTwinTransversal G R := by
  refine ⟨Set.range (fun q : Quotient (twinSetoid G) => q.out), ⟨?_, ?_⟩⟩
  · intro v
    refine ⟨(Quotient.mk (twinSetoid G) v).out, ⟨_, rfl⟩, ?_⟩
    have h : IsTwin G (Quotient.mk (twinSetoid G) v).out v :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (twinSetoid G) v))
    exact h.symm
  · rintro _ ⟨q₁, rfl⟩ _ ⟨q₂, rfl⟩ h
    have key : Quotient.mk (twinSetoid G) q₁.out = Quotient.mk (twinSetoid G) q₂.out :=
      Quotient.sound h
    rw [Quotient.out_eq, Quotient.out_eq] at key
    rw [key]

end Twins

/-! ## Line graphs -/

/-- Paper, Definition (Johnson Graphs and Line Graphs): `H` is an induced subgraph of `J(U,2)`. -/
def IsLineGraph {W : Type u} (H : SimpleGraph W) : Prop :=
  ∃ (U : Type u) (f : W → Sym2 U), (∀ w, ¬ (f w).IsDiag) ∧ Injective f ∧
    ∀ a b, a ≠ b → (H.Adj a b ↔ ∃ x, x ∈ f a ∧ x ∈ f b)

/-- Line graphs are closed under taking induced subgraphs. -/
theorem IsLineGraph.induce {W : Type u} {H : SimpleGraph W} (h : IsLineGraph H) (R : Set W) :
    IsLineGraph (H.induce R) := by
  obtain ⟨U, f, hdiag, hinj, hadj⟩ := h
  refine ⟨U, fun r => f r.1, fun r => hdiag r.1, ?_, ?_⟩
  · intro a b hab
    exact Subtype.ext (hinj hab)
  · intro a b hab
    exact hadj a.1 b.1 (fun h => hab (Subtype.ext h))

/-- Two 2-subsets meet iff some pair of their elements coincide. -/
theorem mem_both_iff {α : Type*} (a b c d : α) :
    (∃ x, x ∈ s(a, b) ∧ x ∈ s(c, d)) ↔ (a = c ∨ a = d ∨ b = c ∨ b = d) := by
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    rw [Sym2.mem_iff] at hx₁ hx₂
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    · exact ⟨_, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
    · exact ⟨_, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    · exact ⟨_, Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩

/-! ## Non-contextual frustration graphs -/

section NC

variable {V : Type u}

/-- `v` is isolated: it commutes with every term (it lies in the set `G` of Definition 1). -/
def IsIsolated (G : SimpleGraph V) (v : V) : Prop := ∀ w, ¬ G.Adj v w

/-- Graph form of Definition 1: commutation (non-adjacency) is transitive on `S'`,
the non-isolated vertices. -/
def IsNCGraph (G : SimpleGraph V) : Prop :=
  ∀ x y z, ¬ IsIsolated G x → ¬ IsIsolated G y → ¬ IsIsolated G z →
    ¬ G.Adj x y → ¬ G.Adj y z → ¬ G.Adj x z

variable {G : SimpleGraph V}

/-- In an NC graph, non-adjacent non-isolated vertices are twins (same partite set). -/
theorem twin_of_not_adj (hG : IsNCGraph G) {a b : V}
    (ha : ¬ IsIsolated G a) (hb : ¬ IsIsolated G b) (hab : ¬ G.Adj a b) : IsTwin G a b := by
  intro w
  constructor
  · intro haw
    by_contra hbw
    have hw : ¬ IsIsolated G w := fun hw => hw a haw.symm
    exact hG a b w ha hb hw hab hbw haw
  · intro hbw
    by_contra haw
    have hw : ¬ IsIsolated G w := fun hw => hw b hbw.symm
    exact hG b a w hb ha hw (fun h => hab h.symm) haw hbw

/-- All isolated vertices are twins of one another. -/
theorem twin_of_isolated {a b : V} (ha : IsIsolated G a) (hb : IsIsolated G b) :
    IsTwin G a b :=
  fun w => ⟨fun h => (ha w h).elim, fun h => (hb w h).elim⟩

variable (G) in
open Classical in
/-- Root-graph labels. Root vertices: `some none` = star centre, `some (some v)` = leaf `v`,
`none` = one extra vertex. A non-isolated representative is the star edge
`{centre, leaf v}`; the (at most one) isolated representative is the disjoint edge
`{leaf v, extra}`. So the reduced graph is `L(K_{1,l} ⊔ K_2)` (or `L(K_{1,l})`). -/
noncomputable def rootLabel (v : V) : Sym2 (Option (Option V)) :=
  if IsIsolated G v then s(some (some v), none) else s(some none, some (some v))

/-- **Theorem 1, graph core.** For a non-contextual frustration graph, every twin reduction
is a line graph. -/
theorem IsNCGraph.twinReduction_isLineGraph (hG : IsNCGraph G)
    {R : Set V} (hR : IsTwinTransversal G R) : IsLineGraph (G.induce R) := by
  refine ⟨Option (Option V), fun r => rootLabel G r.1, ?_, ?_, ?_⟩
  · -- every label is a genuine 2-element subset
    intro r
    by_cases hr : IsIsolated G r.1 <;> simp [rootLabel, hr, Sym2.mk_isDiag_iff]
  · -- labels are injective
    intro r s hrs
    have h : rootLabel G r.1 = rootLabel G s.1 := hrs
    apply Subtype.ext
    simp only [rootLabel] at h
    by_cases hr : IsIsolated G r.1 <;> by_cases hs : IsIsolated G s.1
    · rw [if_pos hr, if_pos hs, Sym2.eq_iff] at h
      simpa using h
    · rw [if_pos hr, if_neg hs, Sym2.eq_iff] at h
      simp at h
    · rw [if_neg hr, if_pos hs, Sym2.eq_iff] at h
      simp at h
    · rw [if_neg hr, if_neg hs, Sym2.eq_iff] at h
      simpa using h
  · -- distinct representatives are adjacent iff their labels meet
    intro a b hab
    have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have hnt : ¬ IsTwin G a.1 b.1 := fun h => hne (hR.unique _ a.2 _ b.2 h)
    change G.Adj a.1 b.1 ↔ ∃ x, x ∈ rootLabel G a.1 ∧ x ∈ rootLabel G b.1
    simp only [rootLabel]
    by_cases ha : IsIsolated G a.1 <;> by_cases hb : IsIsolated G b.1
    · -- two isolated representatives would be twins
      exact absurd (twin_of_isolated ha hb) hnt
    · rw [if_pos ha, if_neg hb, mem_both_iff]
      refine ⟨fun h => (ha b.1 h).elim, fun h => ?_⟩
      exfalso
      simp [hne, hab] at h
    · rw [if_neg ha, if_pos hb, mem_both_iff]
      refine ⟨fun h => (hb a.1 h.symm).elim, fun h => ?_⟩
      exfalso
      simp [hne, hab] at h
    · -- two non-isolated representatives: not twins, hence adjacent
      rw [if_neg ha, if_neg hb, mem_both_iff]
      refine ⟨fun _ => Or.inl rfl, fun _ => ?_⟩
      by_contra h
      exact hnt (twin_of_not_adj hG ha hb h)

end NC

end FermionicNC
