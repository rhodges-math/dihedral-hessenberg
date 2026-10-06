import Schubert.DihedralSplines.Grading
import Schubert.Dihedral.RootPolynomialAction
import Schubert.Dihedral.BruhatOrder
import Schubert.DihedralSplines.HessenbergDegree
import Schubert.Splines.SingleVertexSpline

/-! # Single-vertex and top Hessenberg splines -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergSpace n hthree)

/-- The product of all incident H-labels is a nonzero homogeneous single-vertex spline. -/
theorem exists_hessenberg_single_vertex_spline (vertex : DihedralGroup n) :
    ∃ value : HessenbergSpline ideal,
      (∀ current, (value : DihedralGroup n → CoordinatePolynomial) current =
        if current = vertex then
          ∏ index ∈ ideal.roots, polynomialAction n vertex (rootPolynomial n index) else 0) ∧
      (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 ∧
      value ∈ (hessenbergGraph ideal).homogeneousPiece ideal.roots.card := by
  classical
  let polynomial := ∏ index ∈ ideal.roots, polynomialAction n vertex (rootPolynomial n index)
  let value : HessenbergSpline ideal := ⟨fun current =>
    if current = vertex then polynomial else 0,
    (dihedralReflectionData n hthree).singleProductFunction_isSpline ideal.roots vertex⟩
  refine ⟨value, fun _ => rfl, ?_, ?_⟩
  · change (if vertex = vertex then polynomial else 0) ≠ 0
    simp only [ite_true]
    exact Finset.prod_ne_zero_iff.mpr (fun index _ =>
      polynomialAction_rootPolynomial_ne_zero n vertex index)
  · intro current
    change (if current = vertex then polynomial else 0).IsHomogeneous ideal.roots.card
    by_cases heq : current = vertex
    · rw [ite_eq_left heq]
      have hproduct := MvPolynomial.IsHomogeneous.prod ideal.roots
        (fun index => polynomialAction n vertex (rootPolynomial n index)) (fun _ => 1)
        (fun index _ => polynomialAction_isHomogeneous n vertex
          (rootPolynomial_isHomogeneous n index))
      simpa [polynomial] using hproduct
    · rw [ite_eq_right heq]
      exact MvPolynomial.isHomogeneous_zero _ _ _

/-- At the longest element, the incident-label product is a qualifying homogeneous top spline. -/
theorem exists_hessenberg_top_spline (vertex : DihedralGroup n)
    (htop : length n hthree vertex = n) :
    ∃ value : HessenbergSpline ideal,
      (∀ current, (value : DihedralGroup n → CoordinatePolynomial) current =
        if current = vertex then
          ∏ index ∈ ideal.roots, polynomialAction n vertex (rootPolynomial n index) else 0) ∧
      (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 ∧
      value ∈ (hessenbergGraph ideal).homogeneousPiece (ideal.length vertex) ∧
      (∀ current, ¬ BruhatLE n hthree vertex current →
        (value : DihedralGroup n → CoordinatePolynomial) current = 0) := by
  obtain ⟨value, hvalue, hnonzero, hhomogeneous⟩ :=
    exists_hessenberg_single_vertex_spline ideal vertex
  have hcard : ideal.length vertex = ideal.roots.card := by
    rw [(length_eq_n_iff_eq_alternatingWord n hthree vertex).mp htop,
      ideal.length_alternatingWord_top]
  refine ⟨value, hvalue, hnonzero, hcard.symm ▸ hhomogeneous, ?_⟩
  intro current hnot
  rw [hvalue]
  apply ite_eq_right
  intro heq
  apply hnot
  rw [heq]
  let := bruhatPartialOrder n hthree
  exact le_refl vertex

end Schubert.DihedralSplines
