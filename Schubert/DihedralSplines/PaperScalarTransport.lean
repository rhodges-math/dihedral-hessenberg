import Schubert.DihedralSplines.PaperIdeal
import Schubert.DihedralSplines.PaperAction
import Schubert.Splines.GraphFinite

/-! # Polynomial scalar equivalences for geometric splines -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- The geometric spline equivalence is linear for constant polynomial scalars. -/
def splineEquiv :
    letI := selected.leftAlgebra hthree
    selected.Spline ≃ₗ[CoordinatePolynomial]
      (dihedralReflectionData n hthree).Spline selected.indices := by
  letI := selected.leftAlgebra hthree
  exact {
    toFun := selected.backendEquiv hthree
    invFun := (selected.backendEquiv hthree).symm
    left_inv := (selected.backendEquiv hthree).left_inv
    right_inv := (selected.backendEquiv hthree).right_inv
    map_add' := (selected.backendEquiv hthree).map_add
    map_smul' := fun _ _ => by apply Subtype.ext; funext vertex; rfl }

/-- Constant polynomial scalars make geometric splines a finite module. -/
theorem module_finite :
    letI := selected.leftAlgebra hthree
    Module.Finite CoordinatePolynomial selected.Spline := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := selected.leftAlgebra hthree
  let := (dihedralReflectionData n hthree).leftSpline_finite selected.indices
  exact Module.Finite.equiv (splineEquiv selected hthree).symm

end Left

namespace Right

/-- The geometric spline equivalence is linear for orbit polynomial scalars. -/
def splineEquiv :
    letI := selected.rightAlgebra hthree
    letI := (dihedralReflectionData n hthree).rightAlgebra selected.indices
    selected.Spline ≃ₗ[CoordinatePolynomial]
      (dihedralReflectionData n hthree).Spline selected.indices := by
  letI := selected.rightAlgebra hthree
  letI := (dihedralReflectionData n hthree).rightAlgebra selected.indices
  exact {
    toFun := selected.backendEquiv hthree
    invFun := (selected.backendEquiv hthree).symm
    left_inv := (selected.backendEquiv hthree).left_inv
    right_inv := (selected.backendEquiv hthree).right_inv
    map_add' := (selected.backendEquiv hthree).map_add
    map_smul' := fun _ _ => by apply Subtype.ext; funext vertex; rfl }

/-- Orbit polynomial scalars make geometric splines a finite module. -/
theorem module_finite :
    letI := selected.rightAlgebra hthree
    Module.Finite CoordinatePolynomial selected.Spline := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := selected.rightAlgebra hthree
  let := (dihedralReflectionData n hthree).rightAlgebra selected.indices
  let := (dihedralReflectionData n hthree).rightSpline_finite selected.indices
  exact Module.Finite.equiv (splineEquiv selected hthree).symm

end Right

end Schubert.Dihedral.RootSubset

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The Hessenberg specialization preserves constant polynomial scalar multiplication. -/
def splineEquiv :
    letI := ideal.toRootSubset.leftAlgebra hthree
    ideal.toRootSubset.Spline ≃ₗ[CoordinatePolynomial] HessenbergSpline ideal.indexed := by
  letI := ideal.toRootSubset.leftAlgebra hthree
  exact {
    toFun := ideal.splineEquiv
    invFun := ideal.splineEquiv.symm
    left_inv := ideal.splineEquiv.left_inv
    right_inv := ideal.splineEquiv.right_inv
    map_add' := ideal.splineEquiv.map_add
    map_smul' := fun _ _ => by apply Subtype.ext; funext vertex; rfl }

end Left

namespace Right

/-- The Hessenberg specialization preserves orbit polynomial scalar multiplication. -/
def splineEquiv :
    letI := ideal.toRootSubset.rightAlgebra hthree
    letI : Algebra CoordinatePolynomial (HessenbergSpline ideal.indexed) :=
      (dihedralReflectionData n hthree).rightAlgebra
        (ideal.indexed.roots : Set (PositiveRootIndex n))
    ideal.toRootSubset.Spline ≃ₗ[CoordinatePolynomial] HessenbergSpline ideal.indexed := by
  letI := ideal.toRootSubset.rightAlgebra hthree
  letI : Algebra CoordinatePolynomial (HessenbergSpline ideal.indexed) :=
    (dihedralReflectionData n hthree).rightAlgebra
      (ideal.indexed.roots : Set (PositiveRootIndex n))
  exact {
    toFun := ideal.splineEquiv
    invFun := ideal.splineEquiv.symm
    left_inv := ideal.splineEquiv.left_inv
    right_inv := ideal.splineEquiv.right_inv
    map_add' := ideal.splineEquiv.map_add
    map_smul' := fun _ _ => by apply Subtype.ext; funext vertex; rfl }

end Right

end Schubert.DihedralSplines.HessenbergIdeal
