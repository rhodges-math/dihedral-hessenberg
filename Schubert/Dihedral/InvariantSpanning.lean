import Schubert.Dihedral.InvariantIntegral

/-! # Explicit spanning over the dihedral invariant algebra

The initial axial powers span the polynomial module over the invariants.
Mixed monomials reduce by powers of uv, and higher powers reduce recursively.
-/

noncomputable section

namespace Schubert.Dihedral

/-- A mixed auxiliary monomial factors by uv when its first exponent is smaller. -/
theorem auxiliary_mixed_powers_eq_of_le (first second : ℕ) (horder : first ≤ second) :
    auxiliaryU ^ first * auxiliaryV ^ second =
      quadraticInvariant ^ first * auxiliaryV ^ (second - first) := by
  have hpower : auxiliaryV ^ second =
      auxiliaryV ^ first * auxiliaryV ^ (second - first) := by
    calc
      _ = auxiliaryV ^ (first + (second - first)) := congrArg _ (by omega)
      _ = _ := pow_add _ _ _
  rw [hpower, quadraticInvariant, mul_pow]
  ring

/-- A mixed auxiliary monomial factors by uv when its second exponent is smaller. -/
theorem auxiliary_mixed_powers_eq_of_ge (first second : ℕ) (horder : second ≤ first) :
    auxiliaryU ^ first * auxiliaryV ^ second =
      quadraticInvariant ^ second * auxiliaryU ^ (first - second) := by
  have hpower : auxiliaryU ^ first =
      auxiliaryU ^ second * auxiliaryU ^ (first - second) := by
    calc
      _ = auxiliaryU ^ (second + (first - second)) := congrArg _ (by omega)
      _ = _ := pow_add _ _ _
  rw [hpower, quadraticInvariant, mul_pow]
  ring

/-- Powers of u reduce by the higher invariant and a mixed monomial. -/
theorem auxiliaryU_power_reduction (n degree : ℕ) :
    auxiliaryU ^ (n + degree) = higherInvariant n * auxiliaryU ^ degree -
      MvPolynomial.C ((-1 : ℂ) ^ n) * (auxiliaryU ^ degree * auxiliaryV ^ n) := by
  rw [higherInvariant, pow_add]
  ring

/-- Powers of v reduce by the higher invariant and a mixed monomial. -/
theorem auxiliaryV_power_reduction (n degree : ℕ) :
    auxiliaryV ^ (n + degree) =
      MvPolynomial.C ((-1 : ℂ) ^ n) * (higherInvariant n * auxiliaryV ^ degree) -
        MvPolynomial.C ((-1 : ℂ) ^ n) * (auxiliaryU ^ n * auxiliaryV ^ degree) := by
  rw [higherInvariant, pow_add]
  linear_combination -auxiliaryV ^ n * auxiliaryV ^ degree * higherInvariant_sign_sq n

/-- A submodule containing the initial axial powers contains all axial powers. -/
theorem auxiliary_powers_mem_invariantSubmodule (n : ℕ) [NeZero n]
    (submodule : Submodule (invariantSubalgebra n) CoordinatePolynomial)
    (hfirst : ∀ degree ≤ n, auxiliaryU ^ degree ∈ submodule)
    (hsecond : ∀ degree < n, auxiliaryV ^ degree ∈ submodule) :
    ∀ degree, auxiliaryU ^ degree ∈ submodule ∧ auxiliaryV ^ degree ∈ submodule := by
  have hmul (scalar : CoordinatePolynomial) (hscalar : scalar ∈ invariantSubalgebra n)
      (polynomial : CoordinatePolynomial) (hpolynomial : polynomial ∈ submodule) :
      scalar * polynomial ∈ submodule :=
    submodule.smul_mem (⟨scalar, hscalar⟩ : invariantSubalgebra n) hpolynomial
  have hquadratic (degree : ℕ) : quadraticInvariant ^ degree ∈ invariantSubalgebra n :=
    (invariantSubalgebra n).pow_mem (_root_.Schubert.Dihedral.Invariants.F2.mem n) degree
  have hsign : MvPolynomial.C ((-1 : ℂ) ^ n) ∈ invariantSubalgebra n :=
    (invariantSubalgebra n).algebraMap_mem _
  have hhigher := higherInvariant_mem_invariantSubalgebra n
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree hinduction =>
    by_cases hsmall : degree ≤ n
    · refine ⟨hfirst degree hsmall, ?_⟩
      by_cases hstrict : degree < n
      · exact hsecond degree hstrict
      have hdegree : degree = n := by omega
      subst degree
      have hequal := auxiliaryV_power_reduction n 0
      simp only [pow_zero, mul_one, add_zero] at hequal
      rw [hequal]
      have hone : (1 : CoordinatePolynomial) ∈ submodule := by
        simpa using hfirst 0 (Nat.zero_le n)
      have hmemHigher : higherInvariant n ∈ submodule := by
        simpa using hmul _ hhigher _ hone
      exact submodule.sub_mem (hmul _ hsign _ hmemHigher)
        (hmul _ hsign _ (hfirst n (Nat.le_refl n)))
    · have hlarge : n < degree := Nat.lt_of_not_ge hsmall
      have hpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      have hfirstlower := (hinduction (degree - n) (by omega)).1
      have hsecondlower := (hinduction (degree - n) (by omega)).2
      have hmixedFirst : auxiliaryU ^ (degree - n) * auxiliaryV ^ n ∈ submodule := by
        by_cases horder : degree - n ≤ n
        · rw [auxiliary_mixed_powers_eq_of_le _ _ horder]
          exact hmul _ (hquadratic _) _ (hinduction _ (by omega)).2
        · rw [auxiliary_mixed_powers_eq_of_ge _ _ (by omega)]
          exact hmul _ (hquadratic _) _ (hinduction _ (by omega)).1
      have hmixedSecond : auxiliaryU ^ n * auxiliaryV ^ (degree - n) ∈ submodule := by
        by_cases horder : n ≤ degree - n
        · rw [auxiliary_mixed_powers_eq_of_le _ _ horder]
          exact hmul _ (hquadratic _) _ (hinduction _ (by omega)).2
        · rw [auxiliary_mixed_powers_eq_of_ge _ _ (by omega)]
          exact hmul _ (hquadratic _) _ (hinduction _ (by omega)).1
      have hdegree : degree = n + (degree - n) := by omega
      constructor
      · rw [congrArg (fun exponent => auxiliaryU ^ exponent) hdegree,
          auxiliaryU_power_reduction]
        exact submodule.sub_mem (hmul _ hhigher _ hfirstlower) (hmul _ hsign _ hmixedFirst)
      · rw [congrArg (fun exponent => auxiliaryV ^ exponent) hdegree,
          auxiliaryV_power_reduction]
        exact submodule.sub_mem (hmul _ hsign _ (hmul _ hhigher _ hsecondlower))
          (hmul _ hsign _ hmixedSecond)

/-- A submodule containing the initial axial powers is the full polynomial module. -/
theorem _root_.Schubert.Dihedral.Invariants.span_eq_top_of_axial_powers (n : ℕ) [NeZero n]
    (submodule : Submodule (invariantSubalgebra n) CoordinatePolynomial)
    (hfirst : ∀ degree ≤ n, auxiliaryU ^ degree ∈ submodule)
    (hsecond : ∀ degree < n, auxiliaryV ^ degree ∈ submodule) : submodule = ⊤ := by
  classical
  have hpowers := auxiliary_powers_mem_invariantSubmodule n submodule hfirst hsecond
  have hmul (scalar : CoordinatePolynomial) (hscalar : scalar ∈ invariantSubalgebra n)
      (polynomial : CoordinatePolynomial) (hpolynomial : polynomial ∈ submodule) :
      scalar * polynomial ∈ submodule :=
    submodule.smul_mem (⟨scalar, hscalar⟩ : invariantSubalgebra n) hpolynomial
  have hmixed (first second : ℕ) : auxiliaryU ^ first * auxiliaryV ^ second ∈ submodule := by
    have hquadratic (degree : ℕ) : quadraticInvariant ^ degree ∈ invariantSubalgebra n :=
      (invariantSubalgebra n).pow_mem (_root_.Schubert.Dihedral.Invariants.F2.mem n) degree
    rcases Nat.le_total first second with horder | horder
    · rw [auxiliary_mixed_powers_eq_of_le _ _ horder]
      exact hmul _ (hquadratic _) _ (hpowers _).2
    · rw [auxiliary_mixed_powers_eq_of_ge _ _ horder]
      exact hmul _ (hquadratic _) _ (hpowers _).1
  apply top_unique
  intro polynomial _
  let coordinates := auxiliaryCoordinateEquiv.symm polynomial
  have hexpand : polynomial = ∑ exponent ∈ coordinates.support,
      MvPolynomial.C (coordinates.coeff exponent) *
        (auxiliaryU ^ exponent 0 * auxiliaryV ^ exponent 1) := by
    calc
      polynomial = auxiliaryCoordinateEquiv coordinates :=
        (auxiliaryCoordinateEquiv.apply_symm_apply polynomial).symm
      _ = _ := by
        conv_lhs => rw [coordinates.as_sum, map_sum]
        apply Finset.sum_congr rfl
        intro exponent _
        rw [auxiliaryCoordinateEquiv_monomial]
        ring
  rw [hexpand]
  exact submodule.sum_mem fun exponent _ =>
    hmul _ ((invariantSubalgebra n).algebraMap_mem _) _ (hmixed _ _)

/-- The 2n axial auxiliary powers span over the invariant algebra. -/
theorem invariant_auxiliary_powers_span_eq_top (n : ℕ) [NeZero n] :
    Submodule.span (invariantSubalgebra n)
      (Set.range (Sum.elim (fun index : Fin (n + 1) => auxiliaryU ^ index.val)
        (fun index : Fin (n - 1) => auxiliaryV ^ (index.val + 1)))) = ⊤ := by
  apply _root_.Schubert.Dihedral.Invariants.span_eq_top_of_axial_powers
  · intro degree hdegree
    apply Submodule.subset_span
    exact ⟨Sum.inl ⟨degree, by omega⟩, rfl⟩
  · intro degree hdegree
    apply Submodule.subset_span
    by_cases hzero : degree = 0
    · subst degree
      exact ⟨Sum.inl ⟨0, by omega⟩, by simp⟩
    · refine ⟨Sum.inr ⟨degree - 1, by omega⟩, ?_⟩
      change auxiliaryV ^ (degree - 1 + 1) = auxiliaryV ^ degree
      congr 1
      omega

end Schubert.Dihedral
