import DihedralHessenberg.Dihedral.ScalarMultiplicity
import DihedralHessenberg.Paper.LeftRemovedMultiplicity
import DihedralHessenberg.Paper.RightRemovedMultiplicity

/-! # Nontrivial scalar survival in coordinate kernels -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Nontrivial scalar characters cannot be removed by the left boundary kernel. -/
theorem removed_scalar_zero (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 1 ≤ half)
    (scalar : FDRep ℂ (DihedralGroup n)) [Simple scalar]
    (hdimension : Module.finrank ℂ scalar = 1)
    (hnot : ¬ Nonempty (scalar ≅ FDRep.of
      (Representation.trivial ℂ (DihedralGroup n) ℂ))) :
    Module.finrank ℂ (scalar ⟶ removedFDRep ideal half) = 0 := by
  classical
  let Index := Option {index : ℕ // index ∈ Finset.Icc 1 half}
  let family : Index → FDRep ℂ (DihedralGroup n)
    | none => FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)
    | some index => frequencyFDRep n (index.val : ℕ)
  let multiplicity : Index → ℕ
    | none => half - 1
    | some index => half + 1 - index.val
  have hclass : (TauCeti.SplitK0.of (removedFDRep ideal half) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
        ∑ index, multiplicity index • TauCeti.SplitK0.of (family index) := by
    rw [Fintype.sum_option]
    change TauCeti.SplitK0.of (removedFDRep ideal half) =
      (half - 1) • TauCeti.SplitK0.of
        (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) +
      ∑ index : {index : ℕ // index ∈ Finset.Icc 1 half},
        (half + 1 - index.val) • TauCeti.SplitK0.of (frequencyFDRep n (index.val : ℕ))
    rw [Finset.univ_eq_attach, Finset.sum_attach (Finset.Icc 1 half)
      (fun index : ℕ => (half + 1 - index) •
        (TauCeti.SplitK0.of (frequencyFDRep n (index : ℕ)) :
          TauCeti.repRing ℂ (DihedralGroup n)))]
    exact removed_frequency_class ideal half hhalf hproper hpositive
  rw [hom_finrank_of_class scalar _ family multiplicity hclass]
  apply Finset.sum_eq_zero
  intro index _
  cases index with
  | none =>
      change (half - 1) * Module.finrank ℂ (scalar ⟶
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) = 0
      let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
        apply (FDRep.simple_iff_isIrreducible _).mpr
        change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
        infer_instance
      rw [FDRep.finrank_hom_simple_simple]
      simp only [hnot, ite_false, mul_zero]
  | some index =>
      change (half + 1 - index.val) * Module.finrank ℂ
        (scalar ⟶ frequencyFDRep n (index.val : ℕ)) = 0
      have hbounds := Finset.mem_Icc.mp index.property
      have hmaximum := ideal.card_lt hproper
      rw [scalar_hom_frequency scalar hdimension index.val (by omega) (by omega), mul_zero]
end Left

namespace Right
/-- Nontrivial scalar characters cannot be removed by the right boundary kernel. -/
theorem removed_scalar_zero (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 0 < half)
    (scalar : FDRep ℂ (DihedralGroup n)) [Simple scalar]
    (hdimension : Module.finrank ℂ scalar = 1)
    (hnot : ¬ Nonempty (scalar ≅ FDRep.of
      (Representation.trivial ℂ (DihedralGroup n) ℂ))) :
    Module.finrank ℂ (scalar ⟶ removedFDRep ideal half) = 0 := by
  classical
  rw [hom_finrank_of_class scalar _
    (fun split : Fin half => RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
      (half - (split.val + 1))) (fun split => split.val + 2) (removed_boundary_class ideal half)]
  apply Finset.sum_eq_zero
  intro split _
  change (split.val + 2) * Module.finrank ℂ (scalar ⟶
    RootSubset.Right.pieceFDRep ideal.toRootSubset hthree (half - (split.val + 1))) = 0
  by_cases hzero : half - (split.val + 1) = 0
  · rw [hzero, hom_iso_finrank scalar (low_zero_iso ideal half hhalf hproper hpositive).some]
    let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
      apply (FDRep.simple_iff_isIrreducible _).mpr
      change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
      infer_instance
    rw [FDRep.finrank_hom_simple_simple]
    simp only [hnot, ite_false, mul_zero]
  · rw [hom_iso_finrank scalar (low_frequency_iso ideal half hhalf hproper
      (half - (split.val + 1)) (Nat.pos_of_ne_zero hzero) (by omega)).some]
    have hmaximum := ideal.card_lt hproper
    rw [scalar_hom_frequency scalar hdimension (half - (split.val + 1))
      (Nat.pos_of_ne_zero hzero) (by omega), mul_zero]
end Right
end Schubert.DihedralSplines.HessenbergIdeal
