import DihedralHessenberg.Paper.SplineRestriction
import DihedralHessenberg.Paper.PaperQuotientAction

/-! # Restriction of geometric coordinate quotients -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} (selected larger : RootSubset n) (hthree : 3 ≤ n)
variable (hsubset : (selected : Set RealPlane) ⊆ larger)

/-- Restriction preserves constant spline representatives. -/
theorem restrict_constant (polynomial : CoordinatePolynomial) :
    selected.restrict larger hsubset (larger.constantHom hthree polynomial) =
      selected.constantHom hthree polynomial := by
  apply Subtype.ext
  rfl

/-- Restriction preserves orbit spline representatives. -/
theorem restrict_orbit (polynomial : CoordinatePolynomial) :
    selected.restrict larger hsubset (larger.orbitHom hthree polynomial) =
      selected.orbitHom hthree polynomial := by
  apply Subtype.ext
  rfl

/-- Restriction commutes with the dot action. -/
theorem restrict_dot (element : DihedralGroup n) (value : larger.Spline) :
    selected.restrict larger hsubset (larger.dot hthree element value) =
      selected.dot hthree element (selected.restrict larger hsubset value) := by
  apply Subtype.ext
  rfl

namespace Left

private theorem restrict_kills (value : larger.Spline) (hvalue : value ∈ ideal larger hthree) :
    quotientMap selected hthree (selected.restrict larger hsubset value) = 0 := by
  have hle : ideal larger hthree ≤ RingHom.ker
      ((quotientMap selected hthree).comp (selected.restrict larger hsubset)).toRingHom := by
    rw [ideal_range]
    apply Ideal.span_le.mpr
    rintro original ⟨coordinate, rfl⟩
    change quotientMap selected hthree
      (selected.restrict larger hsubset (larger.constantHom hthree (MvPolynomial.X coordinate))) = 0
    rw [selected.restrict_constant]
    exact coordinate_zero selected hthree coordinate
  exact hle hvalue

/-- Forget reflection conditions on the left coordinate quotients. -/
def restrict : Quotient larger hthree →ₐ[ℂ] Quotient selected hthree :=
  Ideal.Quotient.liftₐ (ideal larger hthree)
    ((quotientMap selected hthree).comp (selected.restrict larger hsubset))
    (fun value hvalue => restrict_kills selected larger hthree hsubset value hvalue)

/-- Quotient restriction preserves spline representatives. -/
theorem restrict_map (value : larger.Spline) :
    restrict selected larger hthree hsubset (quotientMap larger hthree value) =
      quotientMap selected hthree (selected.restrict larger hsubset value) := rfl

/-- Quotient restriction preserves homogeneous degree pieces. -/
theorem restrict_mem_piece (degree : ℕ) (value : Quotient larger hthree)
    (hvalue : value ∈ piece larger hthree degree) :
    restrict selected larger hthree hsubset value ∈ piece selected hthree degree := by
  obtain ⟨original, horiginal, rfl⟩ := (mem_piece larger hthree degree value).mp hvalue
  rw [restrict_map]
  exact (mem_piece selected hthree degree _).mpr
    ⟨selected.restrict larger hsubset original, horiginal, rfl⟩

/-- Quotient restriction intertwines the dot representations. -/
theorem restrict_dot (element : DihedralGroup n) (value : Quotient larger hthree) :
    restrict selected larger hthree hsubset (dotEquiv larger hthree element value) =
      dotEquiv selected hthree element (restrict selected larger hthree hsubset value) := by
  obtain ⟨original, rfl⟩ := map_surjective larger hthree value
  rw [dot_map, restrict_map, restrict_map, dot_map, RootSubset.restrict_dot]

end Left

namespace Right

private theorem restrict_kills (value : larger.Spline) (hvalue : value ∈ ideal larger hthree) :
    quotientMap selected hthree (selected.restrict larger hsubset value) = 0 := by
  have hle : ideal larger hthree ≤ RingHom.ker
      ((quotientMap selected hthree).comp (selected.restrict larger hsubset)).toRingHom := by
    rw [ideal_range]
    apply Ideal.span_le.mpr
    rintro original ⟨coordinate, rfl⟩
    change quotientMap selected hthree
      (selected.restrict larger hsubset (larger.orbitHom hthree (MvPolynomial.X coordinate))) = 0
    rw [selected.restrict_orbit]
    exact coordinate_zero selected hthree coordinate
  exact hle hvalue

/-- Forget reflection conditions on the right coordinate quotients. -/
def restrict : Quotient larger hthree →ₐ[ℂ] Quotient selected hthree :=
  Ideal.Quotient.liftₐ (ideal larger hthree)
    ((quotientMap selected hthree).comp (selected.restrict larger hsubset))
    (fun value hvalue => restrict_kills selected larger hthree hsubset value hvalue)

/-- Quotient restriction preserves spline representatives. -/
theorem restrict_map (value : larger.Spline) :
    restrict selected larger hthree hsubset (quotientMap larger hthree value) =
      quotientMap selected hthree (selected.restrict larger hsubset value) := rfl

/-- Quotient restriction preserves homogeneous degree pieces. -/
theorem restrict_mem_piece (degree : ℕ) (value : Quotient larger hthree)
    (hvalue : value ∈ piece larger hthree degree) :
    restrict selected larger hthree hsubset value ∈ piece selected hthree degree := by
  obtain ⟨original, horiginal, rfl⟩ := (mem_piece larger hthree degree value).mp hvalue
  rw [restrict_map]
  exact (mem_piece selected hthree degree _).mpr
    ⟨selected.restrict larger hsubset original, horiginal, rfl⟩

/-- Quotient restriction intertwines the dot representations. -/
theorem restrict_dot (element : DihedralGroup n) (value : Quotient larger hthree) :
    restrict selected larger hthree hsubset (dotEquiv larger hthree element value) =
      dotEquiv selected hthree element (restrict selected larger hthree hsubset value) := by
  obtain ⟨original, rfl⟩ := map_surjective larger hthree value
  rw [dot_map, restrict_map, restrict_map, dot_map, RootSubset.restrict_dot]

end Right

end Schubert.Dihedral.RootSubset
