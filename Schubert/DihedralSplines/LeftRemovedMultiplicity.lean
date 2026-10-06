import Schubert.Dihedral.FrequencyMultiplicity
import Schubert.DihedralSplines.HessenbergRemovedClass

/-! # Exact frequency multiplicities removed from the boundary spline degree -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The removed kernel has its precise positive-frequency multiplicities. -/
theorem removed_frequency_multiplicity (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 1 ≤ half)
    (frequency : ℕ) (hfrequency : 0 < frequency) (hbelow : 2 * frequency < n) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶ removedFDRep ideal half) =
      if frequency ≤ half then half + 1 - frequency else 0 := by
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
  rw [hom_finrank_of_class _ _ family multiplicity hclass, Fintype.sum_option]
  change (half - 1) * Module.finrank ℂ
      (frequencyFDRep n frequency ⟶
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) +
    ∑ index : {index : ℕ // index ∈ Finset.Icc 1 half}, (half + 1 - index.val) *
      Module.finrank ℂ (frequencyFDRep n frequency ⟶ frequencyFDRep n (index.val : ℕ)) = _
  let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
    apply (FDRep.simple_iff_isIrreducible _).mpr
    change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
    infer_instance
  rw [frequency_hom_scalar frequency hfrequency hbelow _ (by
    change Module.finrank ℂ ℂ = 1
    simp), mul_zero, zero_add]
  have hhalfBelow : 2 * half < n := lt_of_le_of_lt hhalf (ideal.card_lt hproper)
  have hsum :
      (∑ index : {index : ℕ // index ∈ Finset.Icc 1 half}, (half + 1 - index.val) *
        Module.finrank ℂ (frequencyFDRep n frequency ⟶ frequencyFDRep n (index.val : ℕ))) =
      ∑ index : {index : ℕ // index ∈ Finset.Icc 1 half},
        (half + 1 - index.val) * (if frequency = index.val then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro index _
    have hbounds := Finset.mem_Icc.mp index.property
    rw [frequency_hom_frequency frequency index.val hfrequency (by omega) hbelow (by omega)]
  rw [hsum]
  by_cases hle : frequency ≤ half
  · rw [ite_eq_left hle]
    let selected : {index : ℕ // index ∈ Finset.Icc 1 half} :=
      ⟨frequency, Finset.mem_Icc.mpr ⟨hfrequency, hle⟩⟩
    rw [Finset.sum_eq_single selected]
    · simp [selected]
    · intro other _ hother
      have hne : frequency ≠ other.val := by
        intro hequal
        apply hother
        exact Subtype.ext hequal.symm
      simp [hne]
    · simp
  · rw [ite_eq_right hle]
    apply Finset.sum_eq_zero
    intro index _
    have hne : frequency ≠ index.val := by
      have hbounds := Finset.mem_Icc.mp index.property
      omega
    simp [hne]

end Schubert.DihedralSplines.HessenbergIdeal.Left
