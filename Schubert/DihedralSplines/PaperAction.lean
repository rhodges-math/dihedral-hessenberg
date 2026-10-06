import Schubert.DihedralSplines.PaperSpline

/-! # Polynomial scalar structures and dot translation on geometric splines -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Constant polynomials embed in the geometric spline algebra. -/
def constantHom : CoordinatePolynomial →ₐ[ℂ] selected.Spline :=
  (selected.backendEquiv hthree).symm.toAlgHom.comp
    ((dihedralReflectionData n hthree).constantHom selected.indices)

/-- Orbit polynomials embed in the geometric spline algebra. -/
def orbitHom : CoordinatePolynomial →ₐ[ℂ] selected.Spline :=
  (selected.backendEquiv hthree).symm.toAlgHom.comp
    ((dihedralReflectionData n hthree).orbitHom selected.indices)

/-- A constant spline has the same polynomial at every vertex. -/
theorem constantHom_apply (polynomial : CoordinatePolynomial) (vertex : DihedralGroup n) :
    (selected.constantHom hthree polynomial : DihedralGroup n → CoordinatePolynomial) vertex =
      polynomial := rfl

/-- An orbit spline applies the geometric polynomial action at its vertex. -/
theorem orbitHom_apply [NeZero n] (polynomial : CoordinatePolynomial)
    (vertex : DihedralGroup n) :
    (selected.orbitHom hthree polynomial : DihedralGroup n → CoordinatePolynomial) vertex =
      polynomialAction n vertex polynomial := rfl

/-- The polynomial algebra structure given by constant splines. -/
@[instance_reducible] def leftAlgebra : Algebra CoordinatePolynomial selected.Spline :=
  (selected.constantHom hthree).toRingHom.toAlgebra

/-- The polynomial algebra structure given by orbit splines. -/
@[instance_reducible] def rightAlgebra : Algebra CoordinatePolynomial selected.Spline :=
  (selected.orbitHom hthree).toRingHom.toAlgebra

/-- The constant spline corresponding to a coordinate variable. -/
def leftCoordinate (coordinate : Fin 2) : selected.Spline :=
  selected.constantHom hthree (MvPolynomial.X coordinate)

/-- The orbit spline corresponding to a coordinate variable. -/
def rightCoordinate (coordinate : Fin 2) : selected.Spline :=
  selected.orbitHom hthree (MvPolynomial.X coordinate)

/-- The first constant coordinate spline. -/
abbrev xLeft := selected.leftCoordinate hthree 0

/-- The second constant coordinate spline. -/
abbrev yLeft := selected.leftCoordinate hthree 1

/-- The first orbit coordinate spline. -/
abbrev xRight := selected.rightCoordinate hthree 0

/-- The second orbit coordinate spline. -/
abbrev yRight := selected.rightCoordinate hthree 1

/-- Constant spline embedding is substitution of the two constant coordinates. -/
theorem constantHom_aeval : selected.constantHom hthree =
    MvPolynomial.aeval (selected.leftCoordinate hthree) := by
  apply MvPolynomial.algHom_ext
  intro coordinate
  change selected.leftCoordinate hthree coordinate =
    MvPolynomial.aeval (selected.leftCoordinate hthree) (MvPolynomial.X coordinate)
  symm
  exact MvPolynomial.aeval_X _ _

/-- Orbit spline embedding is substitution of the two orbit coordinates. -/
theorem orbitHom_aeval : selected.orbitHom hthree =
    MvPolynomial.aeval (selected.rightCoordinate hthree) := by
  apply MvPolynomial.algHom_ext
  intro coordinate
  change selected.rightCoordinate hthree coordinate =
    MvPolynomial.aeval (selected.rightCoordinate hthree) (MvPolynomial.X coordinate)
  symm
  exact MvPolynomial.aeval_X _ _

/-- Left scalar multiplication substitutes constant coordinate splines and multiplies. -/
theorem left_formula (polynomial : CoordinatePolynomial) (value : selected.Spline) :
    letI := selected.leftAlgebra hthree
    polynomial • value =
      MvPolynomial.aeval (selected.leftCoordinate hthree) polynomial * value := by
  change selected.constantHom hthree polynomial * value = _
  rw [constantHom_aeval]

/-- Right scalar multiplication substitutes orbit coordinate splines and multiplies. -/
theorem right_formula (polynomial : CoordinatePolynomial) (value : selected.Spline) :
    letI := selected.rightAlgebra hthree
    polynomial • value =
      MvPolynomial.aeval (selected.rightCoordinate hthree) polynomial * value := by
  change selected.orbitHom hthree polynomial * value = _
  rw [orbitHom_aeval]

/-- Dot translation is the transported action on the geometric function algebra. -/
def dot (element : DihedralGroup n) (value : selected.Spline) : selected.Spline :=
  (selected.backendEquiv hthree).symm
    ((dihedralReflectionData n hthree).dot selected.indices element
      (selected.backendEquiv hthree value))

/-- Dot translation has the geometric polynomial evaluation formula. -/
theorem dot_apply [NeZero n] (element : DihedralGroup n) (value : selected.Spline)
    (vertex : DihedralGroup n) :
    (selected.dot hthree element value : DihedralGroup n → CoordinatePolynomial) vertex =
      polynomialAction n element
        ((value : DihedralGroup n → CoordinatePolynomial) (element⁻¹ * vertex)) := rfl

/-- The identity dot translation fixes every geometric spline. -/
theorem dot_one (value : selected.Spline) : selected.dot hthree 1 value = value := by
  apply (selected.backendEquiv hthree).injective
  change (dihedralReflectionData n hthree).dot selected.indices 1
    (selected.backendEquiv hthree value) = selected.backendEquiv hthree value
  exact (dihedralReflectionData n hthree).dot_one _ _

/-- Group multiplication composes the geometric dot translations. -/
theorem dot_mul (first second : DihedralGroup n) (value : selected.Spline) :
    selected.dot hthree (first * second) value =
      selected.dot hthree first (selected.dot hthree second value) := by
  apply (selected.backendEquiv hthree).injective
  change (dihedralReflectionData n hthree).dot selected.indices (first * second)
      (selected.backendEquiv hthree value) =
    (dihedralReflectionData n hthree).dot selected.indices first
      ((dihedralReflectionData n hthree).dot selected.indices second
        (selected.backendEquiv hthree value))
  exact (dihedralReflectionData n hthree).dot_mul _ _ _ _

/-- The geometric dot translation is a complex algebra automorphism. -/
def dotEquiv (element : DihedralGroup n) : selected.Spline ≃ₐ[ℂ] selected.Spline :=
  ((selected.backendEquiv hthree).trans
    ((dihedralReflectionData n hthree).dotEquiv selected.indices element)).trans
    (selected.backendEquiv hthree).symm

/-- The transported algebra automorphism is the pointwise dot translation. -/
theorem dotEquiv_apply (element : DihedralGroup n) (value : selected.Spline) :
    selected.dotEquiv hthree element value = selected.dot hthree element value := rfl

/-- Dot translation is a group action by complex algebra automorphisms. -/
def dotAction : DihedralGroup n →* (selected.Spline ≃ₐ[ℂ] selected.Spline) where
  toFun := selected.dotEquiv hthree
  map_one' := by
    apply AlgEquiv.ext
    intro value
    exact selected.dot_one hthree value
  map_mul' first second := by
    apply AlgEquiv.ext
    intro value
    exact selected.dot_mul hthree first second value

end Schubert.Dihedral.RootSubset
