import DihedralHessenberg.Paper.CoinvariantPattern
import DihedralHessenberg.Paper.CoinvariantFrequencyEmbedding
import DihedralHessenberg.Paper.TopRepresentation
import DihedralHessenberg.Dihedral.CoinvariantBoundary

/-! # Quotient embeddings of reflected coinvariant constituents -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The trivial, frequency, and determinant objects in the reflected degree distribution. -/
def coSource (degree : ℕ) : FDRep ℂ (DihedralGroup n) :=
  if degree = 0 then FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)
  else if degree = ideal.carrier.ncard then signFDRep n
  else frequencyFDRep n (min degree (ideal.carrier.ncard - degree) : ℕ)

/-- Each reflected constituent embeds into its homogeneous right quotient. -/
theorem coSource_embedding (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    ∃ embedding : Representation.IntertwiningMap (coSource ideal degree).ρ
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective embedding := by
  by_cases hzero : degree = 0
  · subst degree
    rw [show coSource ideal 0 =
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ) by simp [coSource]]
    obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
      ⟨(Coinvariant.zero_iso n hthree).some.symm⟩
    refine ⟨(ideal.toRootSubset.coinvariantPieceMap hthree 0).comp
      equivalence.toIntertwiningMap, ?_⟩
    exact (ideal.coinvariantPieceMap_injective 0 (by omega) 0 le_rfl).comp
      equivalence.toLinearEquiv.injective
  by_cases htop : degree = ideal.carrier.ncard
  · subst degree
    rw [show coSource ideal ideal.carrier.ncard = signFDRep n by simp [coSource, hzero]]
    obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
      ⟨(top_iso ideal).some.symm⟩
    exact ⟨equivalence.toIntertwiningMap, equivalence.toLinearEquiv.injective⟩
  have hinterior : degree < ideal.carrier.ncard := lt_of_le_of_ne hdegree htop
  by_cases hlower : 2 * degree ≤ ideal.carrier.ncard
  · have hmin : min degree (ideal.carrier.ncard - degree) = degree := by omega
    rw [show coSource ideal degree = frequencyFDRep n degree by
      simp [coSource, hzero, htop, hmin]]
    exact lower_frequency_embedding ideal hproper degree (Nat.pos_of_ne_zero hzero) hlower
  · have hmin : min degree (ideal.carrier.ncard - degree) =
        ideal.carrier.ncard - degree := by omega
    rw [show coSource ideal degree =
      frequencyFDRep n (ideal.carrier.ncard - degree : ℕ) by
      simp [coSource, hzero, htop, hmin]]
    exact upper_frequency_embedding ideal hproper degree hinterior (by omega)

/-- The constituent object has exactly the corresponding finite class coefficient. -/
theorem coSource_class (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    (TauCeti.SplitK0.of (coSource ideal degree) : TauCeti.repRing ℂ (DihedralGroup n)) =
      PowerSeries.coeff degree ideal.coClass := by
  rw [coClass_coeff]
  by_cases hzero : degree = 0
  · simp only [coSource, hzero, ite_true]
  by_cases htop : degree = ideal.carrier.ncard
  · subst degree
    simp only [coSource, hzero, ite_false, ite_true]
  have hinterior : degree < ideal.carrier.ncard := lt_of_le_of_ne hdegree htop
  simp only [coSource, hzero, htop, hinterior, ite_false, ite_true]

end Schubert.DihedralSplines.HessenbergIdeal.Right
