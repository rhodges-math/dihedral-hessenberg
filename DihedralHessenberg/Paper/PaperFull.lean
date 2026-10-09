import DihedralHessenberg.Paper.PaperIdeal
import DihedralHessenberg.Paper.FullLeftEdges

/-! # Full-root geometric spline conditions -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

/-- The subset containing every positive root vector. -/
def full (n : ℕ) : RootSubset n where
  carrier := positiveRoots n
  positive := fun _ hmem => hmem

/-- All numbered positive roots belong to the full vector subset. -/
theorem full_indices (n : ℕ) : (full n).indices = Set.univ := by
  ext index
  exact iff_of_true ⟨index, rfl⟩ (Set.mem_univ index)

/-- Full geometric splines satisfy exactly the fixed-form left reflection conditions. -/
theorem full_iff_left (n : ℕ) (hthree : 3 ≤ n)
    (value : DihedralGroup n → CoordinatePolynomial) :
    (full n).IsSpline value ↔ ∀ vertex (alpha : PositiveRoot n),
      alpha.form ∣ value vertex - value (alpha.reflection * vertex) := by
  rw [(full n).isSpline_iff_backend hthree, full_indices,
    fullReflectionGraph_isSpline_iff_left]
  constructor
  · intro hvalue vertex alpha
    simpa only [PositiveRoot.form_index, PositiveRoot.reflection] using
      hvalue vertex alpha.index
  · intro hvalue vertex index
    simpa only [PositiveRoot.form_equiv, PositiveRoot.reflection_equiv] using
      hvalue vertex (positiveRootEquiv n index)

/-- The subalgebra defined by the fixed-form left reflection conditions. -/
def leftSplineAlgebra (n : ℕ) (hthree : 3 ≤ n) :
    Subalgebra ℂ (DihedralGroup n → CoordinatePolynomial) where
  carrier := {value | ∀ vertex (alpha : PositiveRoot n),
    alpha.form ∣ value vertex - value (alpha.reflection * vertex)}
  algebraMap_mem' scalar := (full_iff_left n hthree _).mp
    ((full n).splineAlgebra.algebraMap_mem scalar)
  add_mem' hfirst hsecond := (full_iff_left n hthree _).mp
    ((full n).splineAlgebra.add_mem ((full_iff_left n hthree _).mpr hfirst)
      ((full_iff_left n hthree _).mpr hsecond))
  mul_mem' hfirst hsecond := (full_iff_left n hthree _).mp
    ((full n).splineAlgebra.mul_mem ((full_iff_left n hthree _).mpr hfirst)
      ((full_iff_left n hthree _).mpr hsecond))

/-- The full geometric function subalgebra equals the fixed-form left subalgebra. -/
theorem full_algebra_eq (n : ℕ) (hthree : 3 ≤ n) :
    (full n).splineAlgebra = leftSplineAlgebra n hthree := by
  ext value
  exact full_iff_left n hthree value

end Schubert.Dihedral.RootSubset

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- The Hessenberg ideal consisting of every positive root vector. -/
def full (n : ℕ) (hthree : 3 ≤ n) : HessenbergIdeal n hthree where
  toRootSubset := RootSubset.full n
  lower := fun {alpha} {_} _ _ => alpha.property
  first_mem := (simpleRoot n hthree 0).property
  second_mem := (simpleRoot n hthree 1).property

/-- A full vector Hessenberg ideal has the fixed-form left reflection condition. -/
theorem full_iff_left (n : ℕ) (hthree : 3 ≤ n)
    (value : DihedralGroup n → CoordinatePolynomial) :
    (full n hthree).toRootSubset.IsSpline value ↔ ∀ vertex (alpha : PositiveRoot n),
      alpha.form ∣ value vertex - value (alpha.reflection * vertex) :=
  RootSubset.full_iff_left n hthree value

/-- The full Hessenberg function subalgebra equals the fixed-form left subalgebra. -/
theorem full_algebra_eq (n : ℕ) (hthree : 3 ≤ n) :
    (full n hthree).toRootSubset.splineAlgebra = RootSubset.leftSplineAlgebra n hthree :=
  RootSubset.full_algebra_eq n hthree

end Schubert.DihedralSplines.HessenbergIdeal
