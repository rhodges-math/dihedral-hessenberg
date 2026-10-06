import Schubert.DihedralSplines.PaperGrading
import Schubert.Splines.SupportLocalization

/-! # Boundary-root products and spline localization -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

/-- Selected positive vectors whose reflection neighbor lies outside the vertex subset. -/
def boundaryRoots (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n) :
    Finset (PositiveRoot n) := by
  classical
  exact Finset.univ.filter
    (fun alpha => alpha.val ∈ selected ∧ vertex * alpha.reflection ∉ vertices)

omit [NeZero n] in
/-- Boundary-root membership is the selected-root and outside-neighbor condition. -/
theorem mem_boundaryRoots (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n)
    (alpha : PositiveRoot n) :
    alpha ∈ selected.boundaryRoots vertices vertex ↔
      alpha.val ∈ selected ∧ vertex * alpha.reflection ∉ vertices := by
  classical
  simp [boundaryRoots]

/-- The product of the exact transformed linear forms on the outgoing boundary edges. -/
def boundaryProduct (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n) :
    CoordinatePolynomial :=
  ∏ alpha ∈ selected.boundaryRoots vertices vertex,
    linearPolynomial (complexify (realAction n vertex alpha.val))

/-- Boundary products have the degree equal to the outgoing-boundary cardinality. -/
theorem boundaryProduct_homogeneous (vertices : Set (DihedralGroup n))
    (vertex : DihedralGroup n) :
    (selected.boundaryProduct vertices vertex).IsHomogeneous
      (selected.boundaryRoots vertices vertex).card := by
  classical
  have hproduct := MvPolynomial.IsHomogeneous.prod (selected.boundaryRoots vertices vertex)
    (fun alpha => linearPolynomial (complexify (realAction n vertex alpha.val)))
    (fun _ => 1) (fun alpha _ => by
      rw [← PositiveRoot.action_form vertex alpha]
      apply polynomialAction_isHomogeneous n vertex
      rw [alpha.form_index]
      exact rootPolynomial_isHomogeneous n alpha.index)
  simpa [boundaryProduct] using hproduct

/-- The product of boundary labels is nonzero, including the empty product. -/
theorem boundaryProduct_ne_zero (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n) :
    selected.boundaryProduct vertices vertex ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro alpha _hmem
  rw [← PositiveRoot.action_form vertex alpha]
  intro hzero
  apply alpha.form_ne_zero
  apply (polynomialAction n vertex).injective
  simpa only [map_zero] using hzero

/-- A spline supported in a vertex subset is divisible by its entire boundary product. -/
theorem boundaryProduct_dvd (vertices : Set (DihedralGroup n)) (value : selected.Spline)
    (hsupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (vertex : DihedralGroup n) :
    selected.boundaryProduct vertices vertex ∣
      (value : DihedralGroup n → CoordinatePolynomial) vertex := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro first _hfirst second _hsecond hne
    change IsRelPrime (linearPolynomial (complexify (realAction n vertex first.val)))
      (linearPolynomial (complexify (realAction n vertex second.val)))
    rw [← PositiveRoot.action_form vertex first, ← PositiveRoot.action_form vertex second]
    exact PositiveRoot.action_relPrime vertex first second hne
  · intro alpha hmem
    obtain ⟨hselected, houtside⟩ := (selected.mem_boundaryRoots vertices vertex alpha).mp hmem
    have hcondition := value.property vertex alpha.val hselected
    have hroot : selected.root alpha.val hselected = alpha := Subtype.ext rfl
    rw [hroot, hsupport _ houtside, sub_zero] at hcondition
    exact hcondition

/-- At its boundary degree, a supported homogeneous spline is a scalar boundary-product multiple. -/
theorem localized (vertices : Set (DihedralGroup n)) (value : selected.Spline) (degree : ℕ)
    (hhomogeneous : value ∈ selected.piece degree)
    (hsupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (vertex : DihedralGroup n) (hcard : (selected.boundaryRoots vertices vertex).card = degree) :
    ∃ scalar : ℂ, (value : DihedralGroup n → CoordinatePolynomial) vertex =
      MvPolynomial.C scalar * selected.boundaryProduct vertices vertex := by
  apply Schubert.Splines.homogeneous_eq_C_mul_of_dvd (degree := degree)
  · rw [← hcard]
    exact selected.boundaryProduct_homogeneous vertices vertex
  · exact hhomogeneous vertex
  · exact selected.boundaryProduct_dvd vertices value hsupport vertex

end Schubert.Dihedral.RootSubset
