import DihedralHessenberg.Splines.Quotient

/-! # Nontriviality of polynomial reflection spline quotients

Evaluation at the identity vertex followed by the constant coefficient kills both
coordinate ideals. Thus neither quotient annihilates the unit.
-/

namespace Schubert.Splines.ReflectionGraphData

variable {K P W T : Type*} [CommRing K] [Group W]
variable (data : ReflectionGraphData K (MvPolynomial P K) W T) (selected : Set T)

/-- The constant-coordinate ideal lies in the identity-vertex augmentation kernel. -/
theorem leftVariableIdeal_le_augmentation_kernel :
    data.leftVariableIdeal selected ≤ RingHom.ker
      (MvPolynomial.constantCoeff.comp
        ((data.reflectionGraph selected).evaluation 1).toRingHom) := by
  rw [data.leftVariableIdeal_eq_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨coordinate, rfl⟩
  change MvPolynomial.constantCoeff ((data.constantSpline selected
    (MvPolynomial.X coordinate) : W → MvPolynomial P K) (1 : W)) = 0
  rw [data.constantSpline_apply, MvPolynomial.constantCoeff_X]

/-- The orbit-coordinate ideal lies in the identity-vertex augmentation kernel. -/
theorem _root_.Schubert.Splines.ReflectionGraphData.right_ideal_le_augmentation_kernel :
    data.rightVariableIdeal selected ≤ RingHom.ker
      (MvPolynomial.constantCoeff.comp
        ((data.reflectionGraph selected).evaluation 1).toRingHom) := by
  rw [data.rightVariableIdeal_eq_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨coordinate, rfl⟩
  change MvPolynomial.constantCoeff ((data.orbitSpline selected
    (MvPolynomial.X coordinate) : W → MvPolynomial P K) (1 : W)) = 0
  rw [data.orbitSpline_apply, map_one, AlgEquiv.one_apply, MvPolynomial.constantCoeff_X]

variable [Nontrivial K]

/-- The constant-coordinate ideal is proper over any nontrivial coefficient ring. -/
theorem leftVariableIdeal_ne_top : data.leftVariableIdeal selected ≠ ⊤ := by
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top _)
    (data.leftVariableIdeal_le_augmentation_kernel selected)

/-- The orbit-coordinate ideal is proper over any nontrivial coefficient ring. -/
theorem rightVariableIdeal_ne_top : data.rightVariableIdeal selected ≠ ⊤ := by
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top _)
    (data.right_ideal_le_augmentation_kernel selected)

/-- The left coordinate quotient is nontrivial. -/
theorem leftQuotient_nontrivial : Nontrivial (data.LeftQuotient selected) :=
  Ideal.Quotient.nontrivial_iff.mpr (data.leftVariableIdeal_ne_top selected)

/-- The right coordinate quotient is nontrivial. -/
theorem rightQuotient_nontrivial : Nontrivial (data.RightQuotient selected) :=
  Ideal.Quotient.nontrivial_iff.mpr (data.rightVariableIdeal_ne_top selected)

end Schubert.Splines.ReflectionGraphData

