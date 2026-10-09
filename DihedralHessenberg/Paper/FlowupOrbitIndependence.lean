import DihedralHessenberg.Paper.FlowupOrbitSupport
import DihedralHessenberg.Paper.BlockSplineIndependence

/-! # Independence of the upper-half spline orbits -/

set_option maxHeartbeats 800000

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

private theorem high_orbit_data (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ∃ block : HessenbergIdeal.Block ideal,
      block.half = n - length n hthree vertex - 1 ∧
      spline ideal vertex ∈ ideal.toRootSubset.piece
        ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
          block.base).card) ∧
      Function.support (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) =
        (block.vertices : Set (DihedralGroup n)) := by
  obtain ⟨block, hbase, hsize, hvertices⟩ :=
    ideal.ascent_block alpha hsimple vertex hascent hhalf hedge
  refine ⟨block, hsize, ?_, ?_⟩
  · have hcard : (ideal.toRootSubset.boundaryRoots
        (block.vertices : Set (DihedralGroup n)) block.base).card =
        ideal.toRootSubset.length vertex := by
      rw [hvertices, hbase, ideal.toRootSubset.boundaryRoots_card]
      let upper := HessenbergIdeal.Upper.ofAscent ideal alpha hsimple vertex hascent hhalf hedge
      exact upper.boundary_card vertex (bruhatLE_refl n hthree vertex)
    rw [hcard]
    exact homogeneous ideal vertex
  · ext current
    rw [Function.mem_support, hvertices]
    exact support_high ideal vertex alpha hsimple hascent hhalf hedge current

/-- Distinct upper-half translates are independent when all short roots are selected. -/
theorem high_orbit_independent {I : Type*} [Fintype I]
    (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hbound : 2 * (n - length n hthree vertex - 1) + 1 < n)
    (hselected : ∀ beta : PositiveRoot n,
      length n hthree beta.reflection ≤ 2 * (n - length n hthree vertex - 1) + 1 →
        beta.val ∈ ideal)
    (translate : I → DihedralGroup n)
    (hinjective : Function.Injective
      (fun index => ideal.toRootSubset.dot hthree (translate index) (spline ideal vertex))) :
    LinearIndependent ℂ
      (fun index => ideal.toRootSubset.dot hthree (translate index) (spline ideal vertex)) := by
  obtain ⟨block, hsize, hhomogeneous, hsupport⟩ :=
    high_orbit_data ideal vertex alpha hsimple hascent hhalf hedge
  apply HessenbergIdeal.Block.orbit_independent ideal block (by simpa only [hsize] using hbound)
    (by simpa only [hsize] using hselected) translate _ (spline ideal vertex) hhomogeneous
  · intro current hnot
    by_contra hnonzero
    have hmem : current ∈ Function.support
        (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) := hnonzero
    rw [hsupport] at hmem
    exact hnot hmem
  · intro hzero
    have heval := congrArg (fun value : ideal.toRootSubset.Spline =>
      (value : DihedralGroup n → CoordinatePolynomial) vertex) hzero
    exact diagonal ideal vertex (by simpa using heval)
  · intro first second heq
    apply hinjective
    apply (high_support_eq ideal vertex alpha hsimple hascent hhalf hedge _ _).mp
    rw [ideal.toRootSubset.dot_support_set hthree,
      ideal.toRootSubset.dot_support_set hthree, hsupport]
    rw [← block.translate_vertices, ← block.translate_vertices]
    exact congrArg (fun vertices : Finset (DihedralGroup n) =>
      (vertices : Set (DihedralGroup n))) heq

/-- Proper odd ideals also give independence of their upper-half spline orbit. -/
theorem high_odd_orbit_independent {I : Type*} [Fintype I]
    (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hcard : ideal.carrier.ncard = 2 * (n - length n hthree vertex - 1) + 1)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (translate : I → DihedralGroup n)
    (hinjective : Function.Injective
      (fun index => ideal.toRootSubset.dot hthree (translate index) (spline ideal vertex))) :
    LinearIndependent ℂ
      (fun index => ideal.toRootSubset.dot hthree (translate index) (spline ideal vertex)) := by
  obtain ⟨block, hsize, hhomogeneous, hsupport⟩ :=
    high_orbit_data ideal vertex alpha hsimple hascent hhalf hedge
  apply HessenbergIdeal.Block.odd_orbit_independent ideal block (by simpa only [hsize] using hcard)
    hproper translate _ (spline ideal vertex) hhomogeneous
  · intro current hnot
    by_contra hnonzero
    have hmem : current ∈ Function.support
        (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) := hnonzero
    rw [hsupport] at hmem
    exact hnot hmem
  · intro hzero
    have heval := congrArg (fun value : ideal.toRootSubset.Spline =>
      (value : DihedralGroup n → CoordinatePolynomial) vertex) hzero
    exact diagonal ideal vertex (by simpa using heval)
  · intro first second heq
    apply hinjective
    apply (high_support_eq ideal vertex alpha hsimple hascent hhalf hedge _ _).mp
    rw [ideal.toRootSubset.dot_support_set hthree,
      ideal.toRootSubset.dot_support_set hthree, hsupport]
    rw [← block.translate_vertices, ← block.translate_vertices]
    exact congrArg (fun vertices : Finset (DihedralGroup n) =>
      (vertices : Set (DihedralGroup n))) heq

/-- A common-half family of high splines is independent on distinct supports. -/
theorem high_family_independent {I : Type*} [Fintype I]
    (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ beta : PositiveRoot n,
      length n hthree beta.reflection ≤ 2 * half + 1 → beta.val ∈ ideal)
    (vertex : I → DihedralGroup n) (alpha : I → PositiveRoot n)
    (hsimple : ∀ index, alpha index = simpleRoot n hthree 0 ∨
      alpha index = simpleRoot n hthree 1)
    (hascent : ∀ index, length n hthree ((alpha index).reflection * vertex index) =
      length n hthree (vertex index) + 1)
    (hhigh : ∀ index, n < 2 * length n hthree (vertex index) + 1)
    (hedge : ∀ index, (vertex index, (alpha index).reflection * vertex index) ∈
      ideal.toRootSubset.edges)
    (hdepth : ∀ index, n - length n hthree (vertex index) - 1 = half)
    (translate : I → DihedralGroup n)
    (hinjective : Function.Injective (fun index => Function.support
      (ideal.toRootSubset.dot hthree (translate index) (spline ideal (vertex index)) :
        DihedralGroup n → CoordinatePolynomial))) :
    LinearIndependent ℂ (fun index =>
      ideal.toRootSubset.dot hthree (translate index) (spline ideal (vertex index))) := by
  classical
  let block : I → HessenbergIdeal.Block ideal := fun index => Classical.choose
    (high_orbit_data ideal (vertex index) (alpha index) (hsimple index)
      (hascent index) (hhigh index) (hedge index))
  have hdata (index) := Classical.choose_spec
    (high_orbit_data ideal (vertex index) (alpha index) (hsimple index)
      (hascent index) (hhigh index) (hedge index))
  have hsupport (index) : Function.support (spline ideal (vertex index) :
      DihedralGroup n → CoordinatePolynomial) =
      ((block index).vertices : Set (DihedralGroup n)) := (hdata index).2.2
  have hnonzero (index) : spline ideal (vertex index) ≠ 0 := by
    intro hzero
    have heval := congrArg (fun value : ideal.toRootSubset.Spline =>
      (value : DihedralGroup n → CoordinatePolynomial) (vertex index)) hzero
    exact diagonal ideal (vertex index) (by simpa using heval)
  have hlocal (index) := (block index).dot_localized (translate index)
    (spline ideal (vertex index)) (hdata index).2.1
    (fun current hnot => by
      by_contra hvalue
      have hmem : current ∈ Function.support
          (spline ideal (vertex index) : DihedralGroup n → CoordinatePolynomial) := hvalue
      rw [hsupport index] at hmem
      exact hnot hmem) (hnonzero index)
  have htranslated (index) : Function.support
      (ideal.toRootSubset.dot hthree (translate index) (spline ideal (vertex index)) :
        DihedralGroup n → CoordinatePolynomial) =
      (((block index).translate (translate index)).vertices : Set (DihedralGroup n)) := by
    rw [ideal.toRootSubset.dot_support_set hthree, hsupport index,
      (block index).translate_vertices]
  refine ideal.block_splines_independent half hbound hselected
    (fun index => (block index).translate (translate index)) ?_ ?_
    (fun index => ideal.toRootSubset.dot hthree (translate index)
      (spline ideal (vertex index))) ?_ ?_ ?_
  · intro index
    exact (hdata index).1.trans (hdepth index)
  · intro first second heq
    apply hinjective
    dsimp only
    rw [htranslated first, htranslated second]
    exact congrArg (fun vertices : Finset (DihedralGroup n) =>
      (vertices : Set (DihedralGroup n))) heq
  · exact fun index => (hlocal index).1
  · exact fun index => (hlocal index).2.1
  · exact fun index => (hlocal index).2.2
end Schubert.DihedralSplines.FlowupSpline
