import DihedralHessenberg.Splines.Quotient
import DihedralHessenberg.Splines.GradedReflectionGraph
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Dot invariance of polynomial spline quotient ideals

The right generators are fixed by dot translation. The left generators translate to
homogeneous linear polynomials, which still belong to the polynomial variable ideal.
-/

namespace Schubert.Splines.GradedReflectionGraphData

universe u v w z

variable {K : Type u} {P : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [Group W]
variable (data : GradedReflectionGraphData K P W T)

/-- A homogeneous linear polynomial lies in the variable ideal. -/
theorem homogeneous_one_mem_idealOfVars (polynomial : MvPolynomial P K)
    (hpolynomial : polynomial.IsHomogeneous 1) :
    polynomial ∈ MvPolynomial.idealOfVars P K := by
  rw [← pow_one (MvPolynomial.idealOfVars P K)]
  apply (MvPolynomial.mem_pow_idealOfVars_iff 1 polynomial).2
  intro exponent hexponent
  have hdegree := hpolynomial (MvPolynomial.mem_support_iff.mp hexponent)
  change (Finsupp.weight (fun _ : P => 1)) exponent = 1 at hdegree
  rw [← Finsupp.degree_eq_weight_one] at hdegree
  omega

/-- Dot translation maps the left variable extension ideal into itself. -/
theorem leftVariableIdeal_dot_le (selected : Set T) (element : W) :
    (data.toReflectionGraphData.leftVariableIdeal selected).map
        (data.toReflectionGraphData.dotEquiv selected element).toRingHom ≤
      data.toReflectionGraphData.leftVariableIdeal selected := by
  apply Ideal.map_le_iff_le_comap.2
  apply le_trans (data.toReflectionGraphData.leftVariableIdeal_eq_span selected).le
  apply Ideal.span_le.2
  rintro value ⟨coordinate, rfl⟩
  change data.toReflectionGraphData.constantSpline selected
      (data.action element (MvPolynomial.X coordinate)) ∈
    data.toReflectionGraphData.leftVariableIdeal selected
  exact Ideal.mem_map_of_mem (data.toReflectionGraphData.constantHom selected).toRingHom
    (homogeneous_one_mem_idealOfVars _
      (data.action_homogeneous element 1 _ (MvPolynomial.isHomogeneous_X K coordinate)))

/-- Dot translation maps the right variable extension ideal into itself. -/
theorem rightVariableIdeal_dot_le (selected : Set T) (element : W) :
    (data.toReflectionGraphData.rightVariableIdeal selected).map
        (data.toReflectionGraphData.dotEquiv selected element).toRingHom ≤
      data.toReflectionGraphData.rightVariableIdeal selected := by
  apply Ideal.map_le_iff_le_comap.2
  apply le_trans (data.toReflectionGraphData.rightVariableIdeal_eq_span selected).le
  apply Ideal.span_le.2
  rintro value ⟨coordinate, rfl⟩
  change data.toReflectionGraphData.dot selected element
      (data.toReflectionGraphData.orbitSpline selected (MvPolynomial.X coordinate)) ∈
    data.toReflectionGraphData.rightVariableIdeal selected
  rw [ReflectionGraphData.dot_orbitSpline]
  rw [ReflectionGraphData.rightVariableIdeal_eq_span]
  exact Ideal.subset_span ⟨coordinate, rfl⟩

/-- Dot translation preserves the left variable extension ideal exactly. -/
theorem leftVariableIdeal_dot_eq (selected : Set T) (element : W) :
    (data.toReflectionGraphData.leftVariableIdeal selected).map
        (data.toReflectionGraphData.dotEquiv selected element).toRingHom =
      data.toReflectionGraphData.leftVariableIdeal selected := by
  apply le_antisymm (data.leftVariableIdeal_dot_le selected element)
  intro value hvalue
  apply (Ideal.mem_map_of_equiv
    (data.toReflectionGraphData.dotEquiv selected element) value).2
  refine ⟨data.toReflectionGraphData.dot selected element⁻¹ value, ?_, ?_⟩
  · exact (Ideal.map_le_iff_le_comap.1
      (data.leftVariableIdeal_dot_le selected element⁻¹)) hvalue
  · exact (data.toReflectionGraphData.dotEquiv selected element).apply_symm_apply value

/-- Dot translation preserves the right variable extension ideal exactly. -/
theorem rightVariableIdeal_dot_eq (selected : Set T) (element : W) :
    (data.toReflectionGraphData.rightVariableIdeal selected).map
        (data.toReflectionGraphData.dotEquiv selected element).toRingHom =
      data.toReflectionGraphData.rightVariableIdeal selected := by
  apply le_antisymm (data.rightVariableIdeal_dot_le selected element)
  intro value hvalue
  apply (Ideal.mem_map_of_equiv
    (data.toReflectionGraphData.dotEquiv selected element) value).2
  refine ⟨data.toReflectionGraphData.dot selected element⁻¹ value, ?_, ?_⟩
  · exact (Ideal.map_le_iff_le_comap.1
      (data.rightVariableIdeal_dot_le selected element⁻¹)) hvalue
  · exact (data.toReflectionGraphData.dotEquiv selected element).apply_symm_apply value

/-- The dot automorphism descends to the left quotient. -/
noncomputable def leftQuotientDotEquiv (selected : Set T) (element : W) :
    data.toReflectionGraphData.LeftQuotient selected ≃ₐ[K]
      data.toReflectionGraphData.LeftQuotient selected :=
  Ideal.quotientEquivAlg _ _ (data.toReflectionGraphData.dotEquiv selected element)
    (data.leftVariableIdeal_dot_eq selected element).symm

/-- The dot automorphism descends to the right quotient. -/
noncomputable def rightQuotientDotEquiv (selected : Set T) (element : W) :
    data.toReflectionGraphData.RightQuotient selected ≃ₐ[K]
      data.toReflectionGraphData.RightQuotient selected :=
  Ideal.quotientEquivAlg _ _ (data.toReflectionGraphData.dotEquiv selected element)
    (data.rightVariableIdeal_dot_eq selected element).symm

/-- Left quotient translation is computed by translating a spline representative. -/
theorem leftQuotientDotEquiv_mk (selected : Set T) (element : W)
    (value : data.toReflectionGraphData.Spline selected) :
    data.leftQuotientDotEquiv selected element
        (Ideal.Quotient.mk _ value) =
      Ideal.Quotient.mk _ (data.toReflectionGraphData.dot selected element value) :=
  Ideal.quotientEquivAlg_mk _ _ _ value

/-- Right quotient translation is computed by translating a spline representative. -/
theorem rightQuotientDotEquiv_mk (selected : Set T) (element : W)
    (value : data.toReflectionGraphData.Spline selected) :
    data.rightQuotientDotEquiv selected element
        (Ideal.Quotient.mk _ value) =
      Ideal.Quotient.mk _ (data.toReflectionGraphData.dot selected element value) :=
  Ideal.quotientEquivAlg_mk _ _ _ value

/-- The descended dot action on the left quotient algebra. -/
noncomputable def leftQuotientDotAction (selected : Set T) :
    W →* (data.toReflectionGraphData.LeftQuotient selected ≃ₐ[K]
      data.toReflectionGraphData.LeftQuotient selected) where
  toFun := data.leftQuotientDotEquiv selected
  map_one' := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨spline, rfl⟩ := Ideal.Quotient.mk_surjective value
    simp only [leftQuotientDotEquiv_mk, ReflectionGraphData.dot_one, AlgEquiv.one_apply]
  map_mul' first second := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨spline, rfl⟩ := Ideal.Quotient.mk_surjective value
    simp only [AlgEquiv.mul_apply, leftQuotientDotEquiv_mk, ReflectionGraphData.dot_mul]

/-- The descended dot action on the right quotient algebra. -/
noncomputable def rightQuotientDotAction (selected : Set T) :
    W →* (data.toReflectionGraphData.RightQuotient selected ≃ₐ[K]
      data.toReflectionGraphData.RightQuotient selected) where
  toFun := data.rightQuotientDotEquiv selected
  map_one' := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨spline, rfl⟩ := Ideal.Quotient.mk_surjective value
    simp only [rightQuotientDotEquiv_mk, ReflectionGraphData.dot_one, AlgEquiv.one_apply]
  map_mul' first second := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨spline, rfl⟩ := Ideal.Quotient.mk_surjective value
    simp only [AlgEquiv.mul_apply, rightQuotientDotEquiv_mk, ReflectionGraphData.dot_mul]

end Schubert.Splines.GradedReflectionGraphData
