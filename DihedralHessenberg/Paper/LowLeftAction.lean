import DihedralHessenberg.Paper.FullLeftAction
import DihedralHessenberg.Paper.LowDegreeQuotientRestriction
import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Paper.HessenbergLowDegree
import DihedralHessenberg.Paper.PaperQuotientFinite
import DihedralHessenberg.Dihedral.AxialLength
import DihedralHessenberg.Paper.DominanceEven

/-! # Fixed low-degree subrepresentations of the left quotient -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every class coming from the full left quotient is fixed by the action. -/
theorem fullPieceMap_fixed (degree : ℕ) (element : DihedralGroup n)
    (value : RootSubset.Left.piece (RootSubset.full n) hthree degree) :
    RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree element
      (fullPieceMap ideal degree value) = fullPieceMap ideal degree value := by
  apply Subtype.ext
  change RootSubset.Left.dotEquiv ideal.toRootSubset hthree element
    (RootSubset.Left.restrict ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive value.val) = _
  exact (RootSubset.Left.restrict_dot ideal.toRootSubset (RootSubset.full n)
    hthree ideal.toRootSubset.positive element value.val).symm.trans
      (congrArg (RootSubset.Left.restrict ideal.toRootSubset (RootSubset.full n)
        hthree ideal.toRootSubset.positive)
        (RootSubset.Left.full_dot_fixed n hthree element value.val))

/-- Below the half threshold, full quotient restriction is a bijection. -/
theorem fullPieceMap_bijective (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree < half) :
    Function.Bijective (fullPieceMap ideal degree) := by
  let := RootSubset.Left.quotient_finite (RootSubset.full n) hthree
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  have hdimension : Module.finrank ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) =
      Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := by
    have hfull := FlowupSpline.Left.piece_finrank (HessenbergIdeal.full n hthree) degree
    change Module.finrank ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) =
      Nat.card {vertex : DihedralGroup n // (RootSubset.full n).length vertex = degree} at hfull
    rw [hfull, FlowupSpline.Left.piece_finrank ideal degree]
    apply Nat.card_congr
    exact (Equiv.refl (DihedralGroup n)).subtypeEquiv (fun vertex => by
      rw [RootSubset.length_full n hthree]
      exact (ideal.length_fiber_below_half half hhalf degree hdegree vertex).symm)
  have hinjective := fullPieceMap_injective ideal half hhalf degree hdegree.le
  exact ⟨hinjective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℂ) (V := RootSubset.Left.piece (RootSubset.full n) hthree degree)
      (V₂ := RootSubset.Left.piece ideal.toRootSubset hthree degree)
      (f := fullPieceMap ideal degree) hdimension).mp hinjective⟩

/-- Every left quotient piece strictly below the threshold has trivial action. -/
theorem low_piece_fixed (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree < half) (element : DihedralGroup n)
    (value : RootSubset.Left.piece ideal.toRootSubset hthree degree) :
    RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree element value = value := by
  obtain ⟨original, rfl⟩ := (fullPieceMap_bijective ideal half hhalf degree hdegree).2 value
  exact fullPieceMap_fixed ideal degree element original

/-- The injected full quotient image has one trivial vector at zero and two thereafter. -/
theorem fullPieceMap_range_finrank (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) (hdegree : degree ≤ half) :
    Module.finrank ℂ (LinearMap.range (fullPieceMap ideal degree)) =
      if degree = 0 then 1 else 2 := by
  let := RootSubset.Left.quotient_finite (RootSubset.full n) hthree
  rw [LinearMap.finrank_range_of_inj (fullPieceMap_injective ideal half hhalf degree hdegree)]
  have hfull := FlowupSpline.Left.piece_finrank (HessenbergIdeal.full n hthree) degree
  change Module.finrank ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) =
    Nat.card {vertex : DihedralGroup n // (RootSubset.full n).length vertex = degree} at hfull
  rw [hfull]
  simp_rw [RootSubset.length_full n hthree]
  rw [length_fiber_card n hthree degree]
  have hmaximum := ideal.card_lt hproper
  have hshort : degree < n := by omega
  simp only [hshort.ne, or_false, hshort, ite_true]
end Schubert.DihedralSplines.HessenbergIdeal.Left
