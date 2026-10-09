import DihedralHessenberg.Dihedral.RootObjects

/-! # Finite unit root-system axioms in the real plane -/

namespace Schubert.Dihedral

/-- The signed root set is symmetric under negation. -/
theorem roots_neg_iff (n : ℕ) (vector : RealPlane) :
    -vector ∈ roots n ↔ vector ∈ roots n := by
  simp only [roots, Set.mem_union, Set.mem_ofPred_eq, neg_neg]
  exact or_comm

/-- The full signed root set is finite. -/
theorem roots_finite (n : ℕ) : (roots n).Finite := by
  have hsubset : roots n ⊆ Set.range (fun pair : Bool × PositiveRootIndex n =>
      if pair.1 then positiveRoot n pair.2 else -positiveRoot n pair.2) := by
    intro vector hvector
    change (∃ index, positiveRoot n index = vector) ∨
      (∃ index, positiveRoot n index = -vector) at hvector
    rcases hvector with ⟨index, hindex⟩ | ⟨index, hindex⟩
    · exact ⟨(true, index), by simpa only [ite_true] using hindex⟩
    · refine ⟨(false, index), ?_⟩
      simp only [Bool.false_eq_true, ite_false, hindex, neg_neg]
  exact (Set.finite_range _).subset hsubset

/-- Each signed root has Euclidean squared length one. -/
theorem roots_unit {n : ℕ} (vector : RealPlane) (hvector : vector ∈ roots n) :
    realBilinearForm vector vector = 1 := by
  change (∃ index, positiveRoot n index = vector) ∨
    (∃ index, positiveRoot n index = -vector) at hvector
  rcases hvector with ⟨index, rfl⟩ | ⟨index, hindex⟩
  · exact positiveRoot_unit n index
  · have hunit := positiveRoot_unit n index
    rw [hindex] at hunit
    simpa only [realBilinearForm, Pi.neg_apply, neg_mul_neg] using hunit

/-- Two proportional unit roots differ by a scalar equal to one or minus one. -/
theorem roots_proportional {n : ℕ} (first second : RealPlane)
    (hfirst : first ∈ roots n) (hsecond : second ∈ roots n) (scalar : ℝ)
    (heq : first = scalar • second) : scalar = 1 ∨ scalar = -1 := by
  have hunit_first := roots_unit first hfirst
  have hunit_second := roots_unit second hsecond
  rw [heq] at hunit_first
  simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul] at hunit_first hunit_second
  have hsquare : scalar ^ 2 = 1 := by nlinarith [hunit_first, hunit_second]
  exact sq_eq_one_iff.mp hsquare

/-- The normal reflection in any signed unit root preserves the full real root set. -/
theorem roots_reflection_mem (n : ℕ) [NeZero n] (normal vector : RealPlane)
    (hnormal : normal ∈ roots n) (hvector : vector ∈ roots n) :
    vector - (2 * realBilinearForm vector normal) • normal ∈ roots n := by
  have hnormal_unit := roots_unit normal hnormal
  have hformula : complexReflection (complexify normal) (complexify vector) =
      complexify (vector - (2 * realBilinearForm vector normal) • normal) := by
    rw [complexReflection_apply, complexBilinearForm_complexify,
      complexBilinearForm_complexify, hnormal_unit, Complex.ofReal_one, div_one]
    funext coordinate
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, complexify,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hoperator : ∃ element : DihedralGroup n,
      vectorOperator n element = complexReflection (complexify normal) := by
    change (∃ index, positiveRoot n index = normal) ∨
      (∃ index, positiveRoot n index = -normal) at hnormal
    rcases hnormal with ⟨index, rfl⟩ | ⟨index, hindex⟩
    · exact ⟨rootReflection index, vectorOperator_rootReflection n index⟩
    · refine ⟨rootReflection index, ?_⟩
      rw [vectorOperator_rootReflection]
      change complexReflection (complexify (positiveRoot n index)) = _
      rw [hindex]
      have hneg : complexify (-normal) = -complexify normal := by
        funext coordinate
        simp only [complexify, Pi.neg_apply, Complex.ofReal_neg]
      rw [hneg, complexReflection_neg]
  obtain ⟨element, helement⟩ := hoperator
  obtain ⟨image, himage, heq⟩ := vectorOperator_complexify_mem_roots n element vector hvector
  rw [helement, hformula] at heq
  have hreal : vector - (2 * realBilinearForm vector normal) • normal = image := by
    funext coordinate
    exact Complex.ofReal_injective (congrFun heq coordinate)
  exact hreal ▸ himage

end Schubert.Dihedral
