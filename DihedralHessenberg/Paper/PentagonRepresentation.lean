import DihedralHessenberg.Paper.WholeQuotientCharacter
import DihedralHessenberg.Paper.PentagonIdeal
import DihedralHessenberg.Paper.LeftOddDegreeClass
import DihedralHessenberg.Dihedral.CosetDecomposition
import DihedralHessenberg.Dihedral.RootCard
import DihedralHessenberg.FiniteGroupCharacters.ClassDimension
import TauCeti.RepresentationTheory.Induction.Permutation
import Mathlib.NumberTheory.Real.Irrational

/-! # The three-root pentagon quotient representation -/

noncomputable section
open scoped BigOperators
open CategoryTheory Limits
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral
open HessenbergIdeal.Left

/-- The three-root carrier is proper in the five-root system. -/
theorem proper : ideal.carrier ≠ positiveRoots 5 := by
  intro h
  have hc := cardinality
  rw [h, positiveRoots_ncard] at hc
  omega

/-- The whole quotient has six trivial and two second-frequency constituents. -/
theorem whole_class :
    (TauCeti.SplitK0.of (wholeFDRep ideal) : TauCeti.repRing ℂ (DihedralGroup 5)) =
      6 + 2 * TauCeti.SplitK0.of (frequencyFDRep 5 2) := by
  obtain ⟨alpha, ⟨_, hdominant⟩, _⟩ := ideal.dominant_odd_unique 1 cardinality proper
  have hpiece (degree : ℕ) := piece_class_odd ideal 1 cardinality proper alpha hdominant degree
  simp_rw [alpha.coset_odd_class (by decide), show (5 - 1) / 2 = 2 by decide,
    Frequency.partialSum_succ 5 1, TauCeti.SplitK0.of_biprod] at hpiece
  rw [HessenbergIdeal.Left.whole_class, cardinality]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hpiece 0, hpiece 1, hpiece 2, hpiece 3]
  norm_num
  ring

/-- The ungraded quotient is six trivial and two frequency objects. -/
theorem whole_iso : Nonempty (wholeFDRep ideal ≅
    (⨁ fun _ : Fin 6 => FDRep.of (Representation.trivial ℂ (DihedralGroup 5) ℂ)) ⊞
    (⨁ fun _ : Fin 2 => frequencyFDRep 5 2)) := by
  apply FDRep.nonempty_iso_of_character_eq
  have heq : (TauCeti.SplitK0.of
      ((⨁ fun _ : Fin 6 => FDRep.of (Representation.trivial ℂ (DihedralGroup 5) ℂ)) ⊞
      (⨁ fun _ : Fin 2 => frequencyFDRep 5 2)) : TauCeti.repRing ℂ (DihedralGroup 5)) =
        6 + 2 * TauCeti.SplitK0.of (frequencyFDRep 5 2) := by
    rw [TauCeti.SplitK0.of_biprod, TauCeti.SplitK0.of_biproduct,
      TauCeti.SplitK0.of_biproduct]
    simp [Schubert.FiniteGroupCharacters.trivial_class_one, nsmul_eq_mul]
  have h := congrArg (TauCeti.repRingCharacter ℂ (DihedralGroup 5)) (whole_class.trans heq.symm)
  simpa only [TauCeti.repRingCharacter_of] using h

/-- The rotation trace of the quotient is the nonintegral pentagon value. -/
theorem rotation_character : (wholeFDRep ideal).character (.r 1) =
    5 - (Real.sqrt 5 : ℂ) := by
  have h := congrArg (fun x : TauCeti.repRing ℂ (DihedralGroup 5) =>
    TauCeti.repRingCharacter ℂ (DihedralGroup 5) x (.r 1)) whole_class
  simp only [map_add, map_mul, map_ofNat, TauCeti.repRingCharacter_of,
    Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply] at h
  rw [frequencyFDRep_character, frequencyRepresentation_character_r] at h
  change (wholeFDRep ideal).character (.r 1) =
    6 + 2 * (2 * (Real.cos (2 * Real.pi * 2 / 5) : ℂ)) at h
  have hangle : 2 * Real.pi * 2 / 5 = Real.pi - Real.pi / 5 := by ring
  rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_five] at h
  push_cast at h
  linear_combination h

/-- No natural fixed-point count equals the quotient's rotation character. -/
theorem rotation_not_nat (count : ℕ) :
    (wholeFDRep ideal).character (.r 1) ≠ (count : ℂ) := by
  rw [rotation_character]
  intro heq
  have hreal := congrArg Complex.re heq
  norm_num at hreal
  have hirr : Irrational (Real.sqrt 5) := by norm_num
  exact hirr ⟨(5 - count : ℚ), by push_cast; linarith⟩

/-- The whole quotient cannot be a finite permutation representation. -/
theorem not_permutation (X : Type*) [Finite X] [MulAction (DihedralGroup 5) X] :
    ¬ Nonempty (Representation.Equiv
      (RootSubset.Left.representation ideal.toRootSubset (by decide))
      (Representation.ofMulAction ℂ (DihedralGroup 5) X)) := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset (by decide)
  rintro ⟨equivalence⟩
  have h := congrFun (Representation.char_iso equivalence) (.r 1)
  rw [TauCeti.char_ofMulAction] at h
  apply rotation_not_nat (Nat.card {x : X // (DihedralGroup.r (1 : ZMod 5)) • x = x})
  rw [show (wholeFDRep ideal).character =
    (RootSubset.Left.representation ideal.toRootSubset (by decide)).character from
      FDRep.character_of _]
  exact h

end Schubert.DihedralSplines.Pentagon
