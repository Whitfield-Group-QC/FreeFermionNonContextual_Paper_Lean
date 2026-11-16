import ContextualityLean.Pauli

/-!
# Theorem 2, layer 1: symplectic linear algebra over 𝔽₂

Phase-free Pauli strings `PauliVec n = 𝔽₂ⁿ × 𝔽₂ⁿ` with the symplectic form `symp`.

* `IsAntiComm a`                     : a family of pairwise anticommuting strings.
* `IsAntiComm.linearIndependent`     : even-size anticommuting families are independent
                                       (so they have at most `2n` members, `card_le`).
* `proj a g`                         : projection of `g` onto the commutant of `a`.
* `IsAntiComm.extend`                : adjoin the pair `P + f, P + f + e` (`P = ∑ a`),
                                       the 𝔽₂ form of `γ̃ = (γ₁⋯γ_{2l}) · μ`.
-/

namespace FermionicNC

open Function

variable {n : ℕ}

/-! ## Arithmetic in `ZMod 2` -/

theorem zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem zmod2_eq_of_add_eq_zero : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide

theorem zmod2_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem card_cast_zero {m : ℕ} (h : Even m) : (m : ZMod 2) = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [Nat.cast_add]
  exact zmod2_add_self _

/-! ## Vectors -/

theorem pv_add_self (v : PauliVec n) : v + v = 0 := by
  ext i <;> simp [zmod2_add_self]

theorem pv_eq_of_add_eq_zero {v w : PauliVec n} (h : v + w = 0) : v = w := by
  calc v = v + (w + w) := by rw [pv_add_self, add_zero]
    _ = (v + w) + w := (add_assoc v w w).symm
    _ = w := by rw [h, zero_add]

theorem finrank_pauliVec : Module.finrank (ZMod 2) (PauliVec n) = 2 * n := by
  change Module.finrank (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) = 2 * n
  rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega

/-! ## Bilinearity of `symp` -/

@[simp] theorem symp_zero_left (q : PauliVec n) : symp 0 q = 0 := by
  simp [symp]

theorem symp_add_left (p p' q : PauliVec n) : symp (p + p') q = symp p q + symp p' q := by
  simp only [symp, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem symp_smul_left (c : ZMod 2) (p q : PauliVec n) : symp (c • p) q = c * symp p q := by
  simp only [symp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem symp_sum_left {κ : Type*} (s : Finset κ) (v : κ → PauliVec n) (w : PauliVec n) :
    symp (∑ i ∈ s, v i) w = ∑ i ∈ s, symp (v i) w := by
  simp only [symp, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_comm

theorem symp_add_right (p q q' : PauliVec n) : symp p (q + q') = symp p q + symp p q' := by
  rw [symp_comm p (q + q'), symp_add_left, symp_comm q p, symp_comm q' p]

theorem symp_smul_right (c : ZMod 2) (p q : PauliVec n) : symp p (c • q) = c * symp p q := by
  rw [symp_comm p (c • q), symp_smul_left, symp_comm q p]

theorem symp_sum_right {κ : Type*} (s : Finset κ) (v : κ → PauliVec n) (w : PauliVec n) :
    symp w (∑ i ∈ s, v i) = ∑ i ∈ s, symp w (v i) := by
  rw [symp_comm w, symp_sum_left]
  exact Finset.sum_congr rfl (fun i _ => symp_comm _ _)

/-- Nondegeneracy: a nonzero string anticommutes with some string. -/
theorem exists_symp_eq_one {p : PauliVec n} (hp : p ≠ 0) : ∃ q, symp p q = 1 := by
  by_cases hx : p.1 = 0
  · have hz : p.2 ≠ 0 := fun hz => hp (Prod.ext hx hz)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    refine ⟨(Pi.single i 1, 0), ?_⟩
    have h : symp p (Pi.single i 1, 0) = p.2 i := by simp [symp, Pi.single_apply]
    rw [h]
    exact zmod2_eq_one_of_ne_zero _ hi
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    refine ⟨(0, Pi.single i 1), ?_⟩
    have h : symp p (0, Pi.single i 1) = p.1 i := by simp [symp, Pi.single_apply]
    rw [h]
    exact zmod2_eq_one_of_ne_zero _ hi

/-! ## Anticommuting families -/

/-- A family of pairwise anticommuting Pauli strings. -/
def IsAntiComm {ι : Type*} (a : ι → PauliVec n) : Prop :=
  ∀ i j, i ≠ j → symp (a i) (a j) = 1

theorem IsAntiComm.comp {ι ι' : Type*} {a : ι → PauliVec n} (ha : IsAntiComm a)
    {φ : ι' → ι} (hφ : Injective φ) : IsAntiComm (a ∘ φ) :=
  fun i j hij => ha (φ i) (φ j) (fun h => hij (hφ h))

theorem IsAntiComm.symp_eq' {ι : Type*} [DecidableEq ι] {a : ι → PauliVec n}
    (ha : IsAntiComm a) (i k : ι) : symp (a i) (a k) = 1 + if i = k then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [symp_self]
    decide
  · rw [ha i k h, add_zero]

/-- Projection onto the commutant of `a`: `g + ∑ᵢ ω(g, aᵢ) (P + aᵢ)` with `P = ∑ⱼ aⱼ`. -/
def proj {ι : Type*} [Fintype ι] (a : ι → PauliVec n) (g : PauliVec n) : PauliVec n :=
  g + ∑ i, symp g (a i) • ((∑ j, a j) + a i)

/-- First new Majorana `P + f`. -/
def maj1 {ι : Type*} [Fintype ι] (a : ι → PauliVec n) (f : PauliVec n) : PauliVec n :=
  (∑ j, a j) + f

/-- Second new Majorana `P + f + e`; the pair sum is `e`. -/
def maj2 {ι : Type*} [Fintype ι] (a : ι → PauliVec n) (f e : PauliVec n) : PauliVec n :=
  maj1 a f + e

/-- `a` extended by the new pair (`false ↦ maj1`, `true ↦ maj2`). -/
def extFamily {ι : Type*} [Fintype ι] (a : ι → PauliVec n) (f e : PauliVec n) :
    ι ⊕ Bool → PauliVec n :=
  Sum.elim a (fun β => cond β (maj2 a f e) (maj1 a f))

section Families

variable {ι : Type*} [Fintype ι] {a : ι → PauliVec n}

/-- `P = ∑ⱼ aⱼ` (the parity) anticommutes with every member of an even family. -/
theorem IsAntiComm.symp_parity (ha : IsAntiComm a) (hev : Even (Fintype.card ι)) (k : ι) :
    symp (∑ j, a j) (a k) = 1 := by
  classical
  rw [symp_sum_left]
  simp only [ha.symp_eq', Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_univ k), card_cast_zero hev, zero_add]

theorem IsAntiComm.linearIndependent (ha : IsAntiComm a) (hev : Even (Fintype.card ι)) :
    LinearIndependent (ZMod 2) a := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ k, (∑ i, g i) + g k = 0 := by
    intro k
    have h := congrArg (fun v => symp v (a k)) hg
    simp only [symp_sum_left, symp_smul_left, ha.symp_eq', mul_add, mul_one, mul_ite, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, symp_zero_left] at h
    rw [if_pos (Finset.mem_univ k)] at h
    exact h
  have hg' : ∀ k, g k = ∑ i, g i := fun k => zmod2_eq_of_add_eq_zero _ _ (key k)
  have hS : ∑ i, g i = 0 := by
    calc ∑ i, g i = ∑ _i : ι, ∑ j, g j := Finset.sum_congr rfl (fun i _ => hg' i)
      _ = (Fintype.card ι : ZMod 2) * ∑ j, g j := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 0 := by rw [card_cast_zero hev, zero_mul]
  intro k
  rw [hg' k, hS]

/-- An even anticommuting family on `n` qubits has at most `2n` members. -/
theorem IsAntiComm.card_le (ha : IsAntiComm a) (hev : Even (Fintype.card ι)) :
    Fintype.card ι ≤ 2 * n := by
  have h := (ha.linearIndependent hev).fintype_card_le_finrank
  rwa [finrank_pauliVec] at h

/-- `P + aᵢ` is dual to `a`: `ω(P + aᵢ, a_k) = δᵢₖ`. -/
theorem IsAntiComm.symp_dual [DecidableEq ι] (ha : IsAntiComm a) (hev : Even (Fintype.card ι))
    (i k : ι) : symp ((∑ j, a j) + a i) (a k) = if i = k then 1 else 0 := by
  rw [symp_add_left, ha.symp_parity hev k, ha.symp_eq' i k]
  split_ifs <;> decide

theorem IsAntiComm.symp_proj (ha : IsAntiComm a) (hev : Even (Fintype.card ι))
    (g : PauliVec n) (k : ι) : symp (proj a g) (a k) = 0 := by
  classical
  rw [proj, symp_add_left, symp_sum_left]
  simp only [symp_smul_left, ha.symp_dual hev, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_univ k)]
  exact zmod2_add_self _

/-- Projecting does not change the form with anything already commuting with `a`. -/
theorem symp_proj_of_perp (g e : PauliVec n) (he : ∀ k, symp e (a k) = 0) :
    symp e (proj a g) = symp e g := by
  have hd : ∀ i, symp e ((∑ j, a j) + a i) = 0 := by
    intro i
    rw [symp_add_right, symp_sum_right, he i, add_zero]
    exact Finset.sum_eq_zero (fun j _ => he j)
  rw [proj, symp_add_right, symp_sum_right]
  simp only [symp_smul_right, hd, mul_zero, Finset.sum_const_zero, add_zero]

/-- If `a` has fewer than `2n` members, its commutant contains a nonzero vector. -/
theorem IsAntiComm.exists_ne_zero_perp (ha : IsAntiComm a) (hev : Even (Fintype.card ι))
    (hlt : Fintype.card ι < 2 * n) : ∃ e : PauliVec n, e ≠ 0 ∧ ∀ k, symp e (a k) = 0 := by
  by_contra hno
  push_neg at hno
  have htop : Submodule.span (ZMod 2) (Set.range a) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    have hp : proj a v = 0 := by
      by_contra hne
      obtain ⟨k, hk⟩ := hno _ hne
      exact hk (ha.symp_proj hev v k)
    have hv : v = ∑ i, symp v (a i) • ((∑ j, a j) + a i) := pv_eq_of_add_eq_zero hp
    rw [hv]
    exact sum_mem (fun i _ => Submodule.smul_mem _ _
      (add_mem (sum_mem (fun j _ => Submodule.subset_span ⟨j, rfl⟩))
        (Submodule.subset_span ⟨i, rfl⟩)))
  have h1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range a)) ≤ Fintype.card ι := by
    apply finrank_range_le_card
  rw [htop] at h1
  simp only [finrank_top] at h1
  rw [finrank_pauliVec] at h1
  omega

theorem IsAntiComm.extFamily_isAntiComm (ha : IsAntiComm a) (hev : Even (Fintype.card ι))
    {f e : PauliVec n} (hf : ∀ k, symp f (a k) = 0) (he : ∀ k, symp e (a k) = 0)
    (hef : symp e f = 1) : IsAntiComm (extFamily a f e) := by
  have hPe : symp (∑ j, a j) e = 0 := by
    rw [symp_sum_left]
    exact Finset.sum_eq_zero (fun j _ => by rw [symp_comm]; exact he j)
  have h1 : ∀ k, symp (maj1 a f) (a k) = 1 := fun k => by
    rw [maj1, symp_add_left, ha.symp_parity hev k, hf k, add_zero]
  have h2 : ∀ k, symp (maj2 a f e) (a k) = 1 := fun k => by
    rw [maj2, symp_add_left, h1 k, he k, add_zero]
  have h12 : symp (maj1 a f) (maj2 a f e) = 1 := by
    rw [maj2, symp_add_right, symp_self, zero_add, maj1, symp_add_left, hPe, zero_add,
      symp_comm f e, hef]
  intro x y hxy
  rcases x with i | β <;> rcases y with j | β'
  · exact ha i j (fun h => hxy (congrArg Sum.inl h))
  · cases β'
    · change symp (a i) (maj1 a f) = 1
      rw [symp_comm]; exact h1 i
    · change symp (a i) (maj2 a f e) = 1
      rw [symp_comm]; exact h2 i
  · cases β
    · change symp (maj1 a f) (a j) = 1
      exact h1 j
    · change symp (maj2 a f e) (a j) = 1
      exact h2 j
  · cases β <;> cases β'
    · exact absurd rfl hxy
    · change symp (maj1 a f) (maj2 a f e) = 1
      exact h12
    · change symp (maj2 a f e) (maj1 a f) = 1
      rw [symp_comm]; exact h12
    · exact absurd rfl hxy

/-- **Extension step.** Given a nonzero `e` commuting with the even family `a`, there is `f`
commuting with `a` with `ω(e, f) = 1`, and `a ∪ {P + f, P + f + e}` is anticommuting. -/
theorem IsAntiComm.extend (ha : IsAntiComm a) (hev : Even (Fintype.card ι)) {e : PauliVec n}
    (he0 : e ≠ 0) (he : ∀ k, symp e (a k) = 0) :
    ∃ f : PauliVec n, (∀ k, symp f (a k) = 0) ∧ symp e f = 1 ∧ IsAntiComm (extFamily a f e) := by
  obtain ⟨g, hg⟩ := exists_symp_eq_one he0
  have hf := ha.symp_proj hev g
  have hef : symp e (proj a g) = 1 := by
    rw [symp_proj_of_perp g e he]
    exact hg
  exact ⟨proj a g, hf, hef, ha.extFamily_isAntiComm hev hf he hef⟩

end Families

end FermionicNC
