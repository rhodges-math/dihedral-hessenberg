import DihedralHessenberg.Dihedral.CoinvariantBoundary
import DihedralHessenberg.Dihedral.CoinvariantFrequency
import DihedralHessenberg.Dihedral.CoinvariantHilbertFunction
import DihedralHessenberg.FiniteGroupCharacters.GradedClass
import DihedralHessenberg.FiniteGroupCharacters.GradedClassFinite

/-! # Exact graded classes of the coinvariant algebra -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral.Coinvariant

/-- The coinvariant degree family defines a representation-ring series. -/
def gradedClass (n : ℕ) [NeZero n] : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
  Schubert.FiniteGroupCharacters.gradedClass (coinvariantGradedRepresentation n)

/-- The coinvariant trace vanishes above the top degree. -/
theorem character_above (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (habove : n < degree) (element : DihedralGroup n) :
    (coinvariantPieceFDRep n degree).character element = 0 := by
  rw [coinvariantPieceFDRep_character]
  let piece := TauCeti.GradedAlgebra.quotientPiece
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree
  have hpiece : piece = ⊥ := Piece.eq_bot_above n hthree degree habove
  let : Subsingleton piece := by rw [hpiece]; infer_instance
  have hoperator : coinvariantPieceRepresentation n degree element = 0 :=
    Subsingleton.elim _ _
  rw [Representation.character, hoperator, map_zero]

/-- The representation-ring class vanishes above the top degree. -/
theorem class_above (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (habove : n < degree) :
    (TauCeti.SplitK0.of (coinvariantPieceFDRep n degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) = 0 := by
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of, map_zero]
  funext element
  exact character_above n hthree degree habove element

/-- Every coefficient is the exact trivial, frequency, sign, or zero class. -/
theorem gradedClass_coeff (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ) :
    PowerSeries.coeff degree (gradedClass n) =
      if degree = 0 then
        (TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) :
          TauCeti.repRing ℂ (DihedralGroup n))
      else if degree = n then TauCeti.SplitK0.of (signFDRep n)
      else if degree < n then TauCeti.SplitK0.of (frequencyFDRep n degree)
      else 0 := by
  rw [gradedClass, Schubert.FiniteGroupCharacters.gradedClass_coeff]
  change TauCeti.SplitK0.of (coinvariantPieceFDRep n degree) = _
  by_cases hzero : degree = 0
  · subst degree
    rw [ite_eq_left rfl]
    obtain ⟨isomorphism⟩ := zero_iso n hthree
    exact TauCeti.SplitK0.of_congr isomorphism
  · rw [ite_eq_right hzero]
    by_cases htop : degree = n
    · subst degree
      rw [ite_eq_left rfl]
      obtain ⟨isomorphism⟩ := top_iso n hthree
      exact TauCeti.SplitK0.of_congr isomorphism
    · rw [ite_eq_right htop]
      by_cases hbelow : degree < n
      · rw [ite_eq_left hbelow]
        obtain ⟨isomorphism⟩ := Middle.frequency_iso n hthree degree (by omega) hbelow
        exact TauCeti.SplitK0.of_congr isomorphism
      · rw [ite_eq_right hbelow]
        exact class_above n hthree degree (by omega)

/-- The graded representation series has no coefficients above its top degree. -/
theorem gradedClass_coeff_above (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (habove : n < degree) : PowerSeries.coeff degree (gradedClass n) = 0 := by
  rw [gradedClass_coeff n hthree]
  simp only [show degree ≠ 0 by omega, show degree ≠ n by omega, habove.not_gt, ite_false]

/-- The coinvariant graded class is a finite sum through its top degree. -/
theorem gradedClass_eq_sum (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    gradedClass n = ∑ degree ∈ Finset.range (n + 1),
      PowerSeries.monomial degree (TauCeti.SplitK0.of (coinvariantPieceFDRep n degree)) := by
  exact Schubert.FiniteGroupCharacters.gradedClass_eq_sum (coinvariantGradedRepresentation n) n
    (fun degree habove => class_above n hthree degree habove)

end Schubert.Dihedral.Coinvariant
