import Schubert.DihedralSplines.PaperAction
import Schubert.DihedralSplines.Grading

/-! # Homogeneous pieces of geometric splines -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

/-- The splines whose polynomial values are homogeneous of a fixed degree. -/
def piece (degree : ℕ) : Submodule ℂ selected.Spline where
  carrier := {value | ∀ vertex,
    ((value : DihedralGroup n → CoordinatePolynomial) vertex).IsHomogeneous degree}
  zero_mem' := fun _ => (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree).zero_mem
  add_mem' hfirst hsecond vertex := (hfirst vertex).add (hsecond vertex)
  smul_mem' scalar _value hvalue vertex :=
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree).smul_mem scalar (hvalue vertex)

/-- Degree-piece membership is polynomial homogeneity at every vertex. -/
theorem mem_piece (degree : ℕ) (value : selected.Spline) :
    value ∈ selected.piece degree ↔ ∀ vertex,
      ((value : DihedralGroup n → CoordinatePolynomial) vertex).IsHomogeneous degree := Iff.rfl

/-- The evaluation-preserving equivalence preserves each homogeneous piece. -/
theorem piece_backend (degree : ℕ) :
    selected.piece degree =
      ((dihedralGradedReflectionData n hthree).homogeneousPiece selected.indices degree).comap
        (selected.backendEquiv hthree).toLinearMap := rfl

/-- Homogeneous projection on geometric splines. -/
def component (degree : ℕ) : selected.Spline →ₗ[ℂ] selected.Spline :=
  (selected.backendEquiv hthree).symm.toLinearMap.comp
    (((dihedralGradedReflectionData n hthree).homogeneousComponent selected.indices degree).comp
      (selected.backendEquiv hthree).toLinearMap)

/-- Homogeneous projection acts on each polynomial value by its standard component. -/
theorem component_apply (degree : ℕ) (value : selected.Spline) (vertex : DihedralGroup n) :
    (selected.component hthree degree value : DihedralGroup n → CoordinatePolynomial) vertex =
      MvPolynomial.homogeneousComponent degree
        ((value : DihedralGroup n → CoordinatePolynomial) vertex) := rfl

/-- Projection belongs to the specified homogeneous spline piece. -/
theorem component_mem (degree : ℕ) (value : selected.Spline) :
    selected.component hthree degree value ∈ selected.piece degree := by
  intro vertex
  exact MvPolynomial.homogeneousComponent_isHomogeneous _ _

/-- Projection fixes a spline in its specified homogeneous piece. -/
theorem component_eq_self (degree : ℕ) (value : selected.Spline)
    (hvalue : value ∈ selected.piece degree) : selected.component hthree degree value = value := by
  apply Subtype.ext
  funext vertex
  exact MvPolynomial.homogeneousComponent_eq_self (hvalue vertex)

/-- Geometric dot translation preserves polynomial homogeneity. -/
theorem dot_mem_piece [NeZero n] (element : DihedralGroup n) (degree : ℕ)
    (value : selected.Spline) (hvalue : value ∈ selected.piece degree) :
    selected.dot hthree element value ∈ selected.piece degree := by
  intro vertex
  exact polynomialAction_isHomogeneous n element (hvalue (element⁻¹ * vertex))

/-- The homogeneous pieces form an internal direct sum for the finite dihedral vertex set. -/
theorem piece_isInternal (hthree : 3 ≤ n) : DirectSum.IsInternal selected.piece := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let backend : ℕ → Submodule ℂ
      ((dihedralReflectionData n hthree).Spline selected.indices) :=
    ((dihedralReflectionData n hthree).reflectionGraph selected.indices).homogeneousPiece
  have hinternal : DirectSum.IsInternal backend :=
    IdealLabeledGraph.homogeneousPiece_isInternal
      ((dihedralReflectionData n hthree).reflectionGraph selected.indices)
      ((dihedralGradedReflectionData n hthree).edgeIdeal_homogeneous selected.indices)
  let transport := (Submodule.orderIsoMapComap
    (selected.backendEquiv hthree).toLinearEquiv).symm
  have hpieces : selected.piece = fun degree => transport (backend degree) := rfl
  rw [hpieces]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (iSupIndep_map_orderIso_iff transport).2 hinternal.submodule_iSupIndep
  · rw [← transport.map_iSup, hinternal.submodule_iSup_eq_top, transport.map_top]

/-- Multiplication adds the degrees of homogeneous splines. -/
theorem pieceGradedMonoid : SetLike.GradedMonoid selected.piece where
  one_mem := fun _ => MvPolynomial.isHomogeneous_one (Fin 2) ℂ
  mul_mem _ _ _ _ hfirst hsecond vertex := (hfirst vertex).mul (hsecond vertex)

/-- The pointwise homogeneous grading of the geometric spline algebra. -/
@[instance_reducible]
def gradedAlgebra (hthree : 3 ≤ n) : GradedAlgebra selected.piece := by
  letI := selected.pieceGradedMonoid
  exact (selected.piece_isInternal hthree).gradedAlgebra

end Schubert.Dihedral.RootSubset
