import DihedralHessenberg.Paper.PaperAction
import DihedralHessenberg.Splines.Quotient
import Mathlib.Tactic.FinCases

/-! # Coordinate quotients of geometric splines -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

private theorem range_two {A : Type*} (value : Fin 2 → A) :
    Set.range value = {value 0, value 1} := by
  ext element
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨coordinate, rfl⟩
    fin_cases coordinate <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

namespace Left

/-- The polynomial variable ideal extended by the left coordinate map. -/
def ideal : Ideal selected.Spline :=
  Ideal.map (selected.constantHom hthree).toRingHom (MvPolynomial.idealOfVars (Fin 2) ℂ)

/-- The defining ideal is spanned by its coordinate splines. -/
theorem ideal_range : ideal selected hthree =
    Ideal.span (Set.range (selected.leftCoordinate hthree)) := by
  change Ideal.map (selected.constantHom hthree).toRingHom
    (Ideal.span (Set.range MvPolynomial.X)) = _
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- The defining ideal has exactly the two displayed coordinate generators. -/
theorem ideal_span : ideal selected hthree =
    Ideal.span {selected.xLeft hthree, selected.yLeft hthree} := by
  rw [ideal_range, range_two]

/-- The defining ideal is the variable ideal times the whole polynomial module. -/
theorem ideal_smul_top :
    letI := selected.leftAlgebra hthree
    (ideal selected hthree).restrictScalars CoordinatePolynomial =
      MvPolynomial.idealOfVars (Fin 2) ℂ •
        (⊤ : Submodule CoordinatePolynomial selected.Spline) := by
  let := selected.leftAlgebra hthree
  exact mapIdeal_restrictScalars_eq_smul_top (MvPolynomial.idealOfVars (Fin 2) ℂ)

/-- The quotient by the two left coordinate splines. -/
abbrev Quotient := selected.Spline ⧸ ideal selected hthree

/-- The canonical complex algebra quotient map. -/
def quotientMap : selected.Spline →ₐ[ℂ] Quotient selected hthree :=
  Ideal.Quotient.mkₐ ℂ (ideal selected hthree)

/-- The quotient map is surjective. -/
theorem map_surjective : Function.Surjective (quotientMap selected hthree) :=
  Ideal.Quotient.mkₐ_surjective ℂ (ideal selected hthree)

/-- The quotient kernel is exactly the coordinate ideal. -/
theorem map_kernel : RingHom.ker (quotientMap selected hthree).toRingHom =
    ideal selected hthree := Ideal.Quotient.mkₐ_ker ℂ _

/-- A spline vanishes in the quotient precisely when it lies in the coordinate ideal. -/
theorem map_zero_iff (value : selected.Spline) :
    quotientMap selected hthree value = 0 ↔ value ∈ ideal selected hthree :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Coordinate splines vanish in their quotient. -/
theorem coordinate_zero (coordinate : Fin 2) :
    quotientMap selected hthree (selected.leftCoordinate hthree coordinate) = 0 := by
  apply (map_zero_iff selected hthree _).2
  rw [ideal_range]
  exact Ideal.subset_span (Set.mem_range_self coordinate)

/-- The geometric coordinate ideal transports to the reflection-graph coordinate ideal. -/
theorem ideal_backend :
    (dihedralReflectionData n hthree).leftVariableIdeal selected.indices =
      Ideal.map (selected.backendEquiv hthree).toRingEquiv.toRingHom (ideal selected hthree) := by
  change Ideal.map _ (MvPolynomial.idealOfVars (Fin 2) ℂ) =
    Ideal.map _ (Ideal.map _ (MvPolynomial.idealOfVars (Fin 2) ℂ))
  rw [Ideal.map_map]
  congr 1

/-- The quotient equivalence induced by the evaluation-preserving spline equivalence. -/
def backendEquiv : Quotient selected hthree ≃ₐ[ℂ]
    (dihedralReflectionData n hthree).LeftQuotient selected.indices :=
  Ideal.quotientEquivAlg _ _ (selected.backendEquiv hthree) (ideal_backend selected hthree)

/-- The quotient equivalence preserves every represented spline. -/
theorem backendEquiv_map (value : selected.Spline) :
    backendEquiv selected hthree (quotientMap selected hthree value) =
      Ideal.Quotient.mkₐ ℂ _ (selected.backendEquiv hthree value) := rfl

end Left

namespace Right

/-- The polynomial variable ideal extended by the right coordinate map. -/
def ideal : Ideal selected.Spline :=
  Ideal.map (selected.orbitHom hthree).toRingHom (MvPolynomial.idealOfVars (Fin 2) ℂ)

/-- The defining ideal is spanned by its coordinate splines. -/
theorem ideal_range : ideal selected hthree =
    Ideal.span (Set.range (selected.rightCoordinate hthree)) := by
  change Ideal.map (selected.orbitHom hthree).toRingHom
    (Ideal.span (Set.range MvPolynomial.X)) = _
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- The defining ideal has exactly the two displayed coordinate generators. -/
theorem ideal_span : ideal selected hthree =
    Ideal.span {selected.xRight hthree, selected.yRight hthree} := by
  rw [ideal_range, range_two]

/-- The defining ideal is the variable ideal times the whole polynomial module. -/
theorem ideal_smul_top :
    letI := selected.rightAlgebra hthree
    (ideal selected hthree).restrictScalars CoordinatePolynomial =
      MvPolynomial.idealOfVars (Fin 2) ℂ •
        (⊤ : Submodule CoordinatePolynomial selected.Spline) := by
  let := selected.rightAlgebra hthree
  exact mapIdeal_restrictScalars_eq_smul_top (MvPolynomial.idealOfVars (Fin 2) ℂ)

/-- The quotient by the two right coordinate splines. -/
abbrev Quotient := selected.Spline ⧸ ideal selected hthree

/-- The canonical complex algebra quotient map. -/
def quotientMap : selected.Spline →ₐ[ℂ] Quotient selected hthree :=
  Ideal.Quotient.mkₐ ℂ (ideal selected hthree)

/-- The quotient map is surjective. -/
theorem map_surjective : Function.Surjective (quotientMap selected hthree) :=
  Ideal.Quotient.mkₐ_surjective ℂ (ideal selected hthree)

/-- The quotient kernel is exactly the coordinate ideal. -/
theorem map_kernel : RingHom.ker (quotientMap selected hthree).toRingHom =
    ideal selected hthree := Ideal.Quotient.mkₐ_ker ℂ _

/-- A spline vanishes in the quotient precisely when it lies in the coordinate ideal. -/
theorem map_zero_iff (value : selected.Spline) :
    quotientMap selected hthree value = 0 ↔ value ∈ ideal selected hthree :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Coordinate splines vanish in their quotient. -/
theorem coordinate_zero (coordinate : Fin 2) :
    quotientMap selected hthree (selected.rightCoordinate hthree coordinate) = 0 := by
  apply (map_zero_iff selected hthree _).2
  rw [ideal_range]
  exact Ideal.subset_span (Set.mem_range_self coordinate)

/-- The geometric coordinate ideal transports to the reflection-graph coordinate ideal. -/
theorem ideal_backend :
    (dihedralReflectionData n hthree).rightVariableIdeal selected.indices =
      Ideal.map (selected.backendEquiv hthree).toRingEquiv.toRingHom (ideal selected hthree) := by
  change Ideal.map _ (MvPolynomial.idealOfVars (Fin 2) ℂ) =
    Ideal.map _ (Ideal.map _ (MvPolynomial.idealOfVars (Fin 2) ℂ))
  rw [Ideal.map_map]
  congr 1

/-- The quotient equivalence induced by the evaluation-preserving spline equivalence. -/
def backendEquiv : Quotient selected hthree ≃ₐ[ℂ]
    (dihedralReflectionData n hthree).RightQuotient selected.indices :=
  Ideal.quotientEquivAlg _ _ (selected.backendEquiv hthree) (ideal_backend selected hthree)

/-- The quotient equivalence preserves every represented spline. -/
theorem backendEquiv_map (value : selected.Spline) :
    backendEquiv selected hthree (quotientMap selected hthree value) =
      Ideal.Quotient.mkₐ ℂ _ (selected.backendEquiv hthree value) := rfl

end Right

end Schubert.Dihedral.RootSubset
