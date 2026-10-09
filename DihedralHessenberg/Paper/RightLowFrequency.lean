import DihedralHessenberg.Paper.CoinvariantFrequencyEmbedding
import DihedralHessenberg.Paper.HessenbergLowDegree
import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Dihedral.AxialLength
import DihedralHessenberg.Paper.CoSourceEmbedding

/-! # Exact frequencies in low right quotient degrees -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Low quotient dimensions are one at zero and two in every positive degree. -/
theorem low_piece_dimension (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) (hdegree : degree < half) :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) =
      if degree = 0 then 1 else 2 := by
  rw [FlowupSpline.Right.piece_finrank ideal degree]
  have hfiber : Nat.card {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree} =
      Nat.card {vertex : DihedralGroup n // length n hthree vertex = degree} :=
    Nat.card_congr ((Equiv.refl (DihedralGroup n)).subtypeEquiv
      (fun vertex => ideal.length_fiber_below_half half hhalf degree hdegree vertex))
  rw [hfiber, length_fiber_card n hthree degree]
  have hmaximum := ideal.card_lt hproper
  have hshort : degree < n := by omega
  simp only [hshort.ne, or_false, hshort, ite_true]

/-- Every positive quotient degree strictly below the threshold has dimension two. -/
theorem low_piece_finrank (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ)
    (hpositive : 0 < degree) (hdegree : degree < half) :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) = 2 := by
  rw [FlowupSpline.Right.piece_finrank ideal degree]
  have hfiber : Nat.card {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree} =
      Nat.card {vertex : DihedralGroup n // length n hthree vertex = degree} :=
    Nat.card_congr ((Equiv.refl (DihedralGroup n)).subtypeEquiv
    (fun vertex => ideal.length_fiber_below_half half hhalf degree hdegree vertex))
  rw [hfiber, length_fiber_card n hthree degree]
  have hmaximum := ideal.card_lt hproper
  have hshort : degree < n := by omega
  simp only [hpositive.ne', hshort.ne, or_self, ite_false, hshort, ite_true]

/-- The degree-zero right quotient is exactly the trivial representation. -/
theorem low_zero_iso (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 0 < half) :
    Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree 0 ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  obtain ⟨embedding, hinjective⟩ := coSource_embedding ideal hproper 0 (by omega)
  have hsource : coSource ideal 0 = FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ) := by
    simp [coSource]
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  have hdimension : Module.finrank ℂ (coSource ideal 0) =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree 0) := by
    rw [hsource, low_piece_dimension ideal half hhalf hproper 0 hpositive]
    simp
  have hsurjective := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hdimension (f := embedding.toLinearMap)).mp hinjective
  have hiso : Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree 0 ≅
      coSource ideal 0) := TauCeti.nonempty_fdRepIso_iff.mpr ⟨(embedding.ofBijective
    ⟨hinjective, hsurjective⟩).symm⟩
  rwa [hsource] at hiso

/-- The low right quotient action is the corresponding frequency representation. -/
theorem low_frequency_iso (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ)
    (hpositive : 0 < degree) (hdegree : degree < half) :
    Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree ≅
      frequencyFDRep n (degree : ℕ)) := by
  obtain ⟨embedding, hinjective⟩ := lower_frequency_embedding ideal hproper degree
    hpositive (by omega)
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  have hdimension : Module.finrank ℂ (frequencyFDRep n (degree : ℕ)) =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := by
    rw [frequencyFDRep_finrank, low_piece_finrank ideal half hhalf hproper
      degree hpositive hdegree]
  have hsurjective := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hdimension (f := embedding.toLinearMap)).mp hinjective
  exact TauCeti.nonempty_fdRepIso_iff.mpr ⟨(embedding.ofBijective
    ⟨hinjective, hsurjective⟩).symm⟩

end Schubert.DihedralSplines.HessenbergIdeal.Right
