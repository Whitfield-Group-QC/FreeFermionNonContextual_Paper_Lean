import ContextualityLean.Symplectic

/-!
# Theorem 2, layer 2: the adapted-extension lemma and the encoding (𝔽₂ form)

`exists_adapted_extension`: an even anticommuting family `a` on `n` qubits, together with a
commuting set `C` in its commutant, extends to `2n` pairwise anticommuting strings whose new
pairs have pair-sums spanning (a space containing) `C`.

`theorem2_symplectic`: the encoding statement of Theorem 2. The specified Majoranas are
given as pairs `a : Fin l × Bool → _`, plus an optional unpaired one `x` (odd `|𝒜|`).

Dictionary to operators (next layers):
* Majoranas `μ`            ↔ the family `Sum.elim a b`;
* `μ_{k,0} + μ_{k,1}`      ↔ `-i μ_{k,0} μ_{k,1} = 1 - 2nₖ`;
* `C ⊆ span(pair sums)`    ↔ each `C_j` is ± a product of `(1 - 2nₖ)`, `k > l`;
* `x + ∑ a ∈ span(...)`    ↔ `γ_{2l+1} ∝ P_{1..l} · Q` with `Q` a product of `(1 - 2nₖ)`
                              (`Q ∝ I` is the paper's Case 1).
-/

namespace FermionicNC

open Function

variable {n : ℕ}

/-- New pairs: `none ↦ (maj1, maj2)`, `some k ↦ b' k`. -/
def extendPairs {ι κ : Type*} [Fintype ι] (a : ι → PauliVec n) (f e : PauliVec n)
    (b' : κ × Bool → PauliVec n) : Option κ × Bool → PauliVec n :=
  fun p => Option.elim p.1 (cond p.2 (maj2 a f e) (maj1 a f)) (fun k => b' (k, p.2))

/-- Reindexing used to compare the family before and after one induction step. -/
def reindex {ι κ : Type*} : ι ⊕ (Option κ × Bool) → (ι ⊕ Bool) ⊕ (κ × Bool) :=
  Sum.elim (fun i => Sum.inl (Sum.inl i))
    (fun p => Option.elim p.1 (Sum.inl (Sum.inr p.2)) (fun k => Sum.inr (k, p.2)))

theorem reindex_injective {ι κ : Type*} : Injective (reindex (ι := ι) (κ := κ)) := by
  rintro (i | ⟨_ | k, β⟩) (i' | ⟨_ | k', β'⟩) h <;> simp_all [reindex, Option.elim]

/-- **Adapted-extension lemma.** -/
theorem exists_adapted_extension (d : ℕ) :
    ∀ {ι : Type} [Fintype ι] (a : ι → PauliVec n),
      IsAntiComm a → Fintype.card ι + 2 * d = 2 * n →
      ∀ C : Set (PauliVec n), (∀ c ∈ C, ∀ c' ∈ C, symp c c' = 0) →
        (∀ c ∈ C, ∀ k, symp c (a k) = 0) →
        ∃ (κ : Type) (_ : Fintype κ) (b : κ × Bool → PauliVec n),
          Fintype.card κ = d ∧ IsAntiComm (Sum.elim a b) ∧
          C ⊆ Submodule.span (ZMod 2) (Set.range fun k : κ => b (k, false) + b (k, true)) := by
  induction d with
  | zero =>
    intro ι _ a ha hcard C hCiso hCa
    have hev : Even (Fintype.card ι) := ⟨n, by omega⟩
    refine ⟨Empty, inferInstance, fun p => p.1.elim, by simp, ?_, ?_⟩
    · intro x y hxy
      rcases x with i | ⟨⟨⟩, _⟩
      rcases y with j | ⟨⟨⟩, _⟩
      exact ha i j (fun h => hxy (congrArg Sum.inl h))
    · -- the commutant of a full family is zero
      intro c hc
      have hc0 : c = 0 := by
        by_contra hne
        obtain ⟨f, -, -, hext⟩ := ha.extend hev hne (hCa c hc)
        have hev' : Even (Fintype.card (ι ⊕ Bool)) := by
          rw [Fintype.card_sum, Fintype.card_bool]
          exact hev.add even_two
        have hle := hext.card_le hev'
        rw [Fintype.card_sum, Fintype.card_bool] at hle
        omega
      rw [hc0]
      exact Submodule.zero_mem _
  | succ d ih =>
    intro ι _ a ha hcard C hCiso hCa
    have hev : Even (Fintype.card ι) := ⟨n - (d + 1), by omega⟩
    -- choose the next pair-sum `e`: an element of `C` if possible
    obtain ⟨e, he0, hea, hce⟩ : ∃ e : PauliVec n, e ≠ 0 ∧ (∀ k, symp e (a k) = 0) ∧
        ∀ c ∈ C, symp c e = 0 := by
      by_cases hC : ∃ c ∈ C, c ≠ 0
      · obtain ⟨c₀, hc₀, hne⟩ := hC
        exact ⟨c₀, hne, hCa c₀ hc₀, fun c hc => hCiso c hc c₀ hc₀⟩
      · push_neg at hC
        obtain ⟨e, he0, hea⟩ := ha.exists_ne_zero_perp hev (by omega)
        exact ⟨e, he0, hea, fun c hc => by rw [hC c hc, symp_zero_left]⟩
    obtain ⟨f, hfa, hef, hext⟩ := ha.extend hev he0 hea
    have hce' : ∀ c ∈ C, symp e c = 0 := fun c hc => by
      rw [symp_comm]
      exact hce c hc
    have hcP : ∀ c ∈ C, symp c (∑ j, a j) = 0 := fun c hc => by
      rw [symp_sum_right]
      exact Finset.sum_eq_zero (fun j _ => hCa c hc j)
    have heP : symp e (∑ j, a j) = 0 := by
      rw [symp_sum_right]
      exact Finset.sum_eq_zero (fun j _ => hea j)
    -- shift `C` so that it commutes with the new pair
    have hiso : ∀ x ∈ (fun c => c + symp c f • e) '' C,
        ∀ y ∈ (fun c => c + symp c f • e) '' C, symp x y = 0 := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
      simp only [symp_add_left, symp_add_right, symp_smul_left, symp_smul_right,
        hCiso c hc c' hc', hce c hc, hce' c' hc', symp_self, mul_zero, add_zero]
    have hperp : ∀ x ∈ (fun c => c + symp c f • e) '' C, ∀ k, symp x (extFamily a f e k) = 0 := by
      rintro _ ⟨c, hc, rfl⟩ (k | β)
      · change symp (c + symp c f • e) (a k) = 0
        simp only [symp_add_left, symp_smul_left, hCa c hc k, hea k, mul_zero, add_zero]
      · cases β
        · change symp (c + symp c f • e) ((∑ j, a j) + f) = 0
          simp only [symp_add_left, symp_add_right, symp_smul_left, hcP c hc, heP, hef,
            zero_add, mul_one, mul_zero, zmod2_add_self]
        · change symp (c + symp c f • e) ((∑ j, a j) + f + e) = 0
          simp only [symp_add_left, symp_add_right, symp_smul_left, hcP c hc, heP, hef,
            hce c hc, symp_self, zero_add, add_zero, mul_one, mul_zero, zmod2_add_self]
    obtain ⟨κ', hκ', b', hcard', hanti', hspan'⟩ := ih (extFamily a f e) hext
      (by rw [Fintype.card_sum, Fintype.card_bool]; omega) _ hiso hperp
    refine ⟨Option κ', inferInstance, extendPairs a f e b', ?_, ?_, ?_⟩
    · rw [Fintype.card_option, hcard']
    · have hcomp : Sum.elim a (extendPairs a f e b') = Sum.elim (extFamily a f e) b' ∘ reindex := by
        funext x
        rcases x with i | ⟨_ | k, β⟩ <;> rfl
      rw [hcomp]
      exact hanti'.comp reindex_injective
    · intro c hc
      have hc' : c + symp c f • e ∈
          Submodule.span (ZMod 2) (Set.range fun k : κ' => b' (k, false) + b' (k, true)) :=
        hspan' ⟨c, hc, rfl⟩
      have hmono : Submodule.span (ZMod 2) (Set.range fun k : κ' => b' (k, false) + b' (k, true))
          ≤ Submodule.span (ZMod 2) (Set.range fun k : Option κ' =>
              extendPairs a f e b' (k, false) + extendPairs a f e b' (k, true)) := by
        apply Submodule.span_mono
        rintro _ ⟨k, rfl⟩
        exact ⟨some k, rfl⟩
      have hpair : extendPairs a f e b' (none, false) + extendPairs a f e b' (none, true) = e := by
        change maj1 a f + (maj1 a f + e) = e
        rw [← add_assoc, pv_add_self, zero_add]
      have he_mem : e ∈ Submodule.span (ZMod 2) (Set.range fun k : Option κ' =>
          extendPairs a f e b' (k, false) + extendPairs a f e b' (k, true)) :=
        Submodule.subset_span ⟨none, hpair⟩
      have hdecomp : c = (c + symp c f • e) + symp c f • e := by
        rw [add_assoc, pv_add_self, add_zero]
      rw [hdecomp]
      exact add_mem (hmono hc') (Submodule.smul_mem _ _ he_mem)

/-- **Theorem 2, encoding (𝔽₂ form).** Specified Majoranas: `l` pairs `a`, plus optionally one
unpaired `x` (odd `|𝒜|`). `C` generates the commuting symmetries. Then `a` extends to a full
`n`-mode Majorana family `Sum.elim a b`, every element of `C` lies in the span of the new pair
sums, and `x + ∑ a` (the 𝔽₂ vector of `P_{1..l}⁻¹ · x`) does too. -/
theorem theorem2_symplectic {l : ℕ} (a : Fin l × Bool → PauliVec n) (ha : IsAntiComm a)
    (extra : Option (PauliVec n)) (hx : ∀ x ∈ extra, ∀ k, symp x (a k) = 1)
    (C : Set (PauliVec n)) (hCiso : ∀ c ∈ C, ∀ c' ∈ C, symp c c' = 0)
    (hCa : ∀ c ∈ C, ∀ k, symp c (a k) = 0) (hCx : ∀ x ∈ extra, ∀ c ∈ C, symp c x = 0) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ × Bool → PauliVec n),
      l + Fintype.card κ = n ∧ IsAntiComm (Sum.elim a b) ∧
      C ⊆ Submodule.span (ZMod 2) (Set.range fun k : κ => b (k, false) + b (k, true)) ∧
      ∀ x ∈ extra, x + ∑ k, a k ∈
        Submodule.span (ZMod 2) (Set.range fun k : κ => b (k, false) + b (k, true)) := by
  have hcardι : Fintype.card (Fin l × Bool) = 2 * l := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have hev : Even (Fintype.card (Fin l × Bool)) := ⟨l, by rw [hcardι]; ring⟩
  have hl : l ≤ n := by
    have := ha.card_le hev
    omega
  cases extra with
  | none =>
    obtain ⟨κ, hκ, b, hcard, hanti, hspan⟩ :=
      exists_adapted_extension (n - l) a ha (by omega) C hCiso hCa
    refine ⟨κ, hκ, b, by omega, hanti, hspan, ?_⟩
    intro x hx'
    simp at hx'
  | some x =>
    have hxa : ∀ k, symp x (a k) = 1 := hx x (by simp)
    have hQa : ∀ k, symp (x + ∑ j, a j) (a k) = 0 := fun k => by
      rw [symp_add_left, hxa k, ha.symp_parity hev k]
      decide
    have hCQ : ∀ c ∈ C, symp c (x + ∑ j, a j) = 0 := fun c hc => by
      rw [symp_add_right, symp_sum_right, hCx x (by simp) c hc, zero_add]
      exact Finset.sum_eq_zero (fun j _ => hCa c hc j)
    have hDiso : ∀ y ∈ insert (x + ∑ j, a j) C, ∀ y' ∈ insert (x + ∑ j, a j) C,
        symp y y' = 0 := by
      rintro y (rfl | hy) y' (rfl | hy')
      · exact symp_self _
      · rw [symp_comm]
        exact hCQ y' hy'
      · exact hCQ y hy
      · exact hCiso y hy y' hy'
    have hDa : ∀ y ∈ insert (x + ∑ j, a j) C, ∀ k, symp y (a k) = 0 := by
      rintro y (rfl | hy)
      · exact hQa
      · exact hCa y hy
    obtain ⟨κ, hκ, b, hcard, hanti, hspan⟩ :=
      exists_adapted_extension (n - l) a ha (by omega) _ hDiso hDa
    refine ⟨κ, hκ, b, by omega, hanti, fun c hc => hspan (Set.mem_insert_of_mem _ hc), ?_⟩
    intro x' hx'
    simp only [Option.mem_def, Option.some.injEq] at hx'
    subst hx'
    exact hspan (Set.mem_insert _ _)

end FermionicNC
