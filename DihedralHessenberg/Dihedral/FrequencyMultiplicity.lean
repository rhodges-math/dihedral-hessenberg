import DihedralHessenberg.FiniteGroupCharacters.MorphismDimension
import DihedralHessenberg.FiniteGroupCharacters.HomMultiplicity
import DihedralHessenberg.Dihedral.FrequencySum
import DihedralHessenberg.Dihedral.CosetDecomposition
import DihedralHessenberg.Dihedral.ScalarFamily

/-! # Frequency constituents in dihedral objects -/

noncomputable section
open CategoryTheory
namespace Schubert.Dihedral
open Schubert.FiniteGroupCharacters
variable {n : ℕ} [NeZero n]

/-- Positive lower-half frequencies have no morphisms into a scalar-dimensional object. -/
theorem frequency_hom_scalar (frequency : ℕ) (hpositive : 0 < frequency)
    (hbelow : 2 * frequency < n) (scalar : FDRep ℂ (DihedralGroup n)) [Simple scalar]
    (hdimension : Module.finrank ℂ scalar = 1) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶ scalar) = 0 := by
  let : Simple (frequencyFDRep n frequency) :=
    frequencyFDRep_simple_of_lower_half n frequency hpositive hbelow
  rw [FDRep.finrank_hom_simple_simple]
  have hnot : ¬ Nonempty (frequencyFDRep n frequency ≅ scalar) := by
    rintro ⟨equivalence⟩
    have htrace := congrFun (FDRep.char_iso equivalence) (1 : DihedralGroup n)
    rw [FDRep.char_one, FDRep.char_one, frequencyFDRep_finrank, hdimension] at htrace
    norm_num at htrace
  simp only [hnot, ite_false]

/-- The frequency prefix contains each of its positive frequencies exactly once. -/
theorem frequency_hom_prefix (frequency : ℕ) (hpositive : 0 < frequency)
    (hbelow : 2 * frequency < n) (endpoint : ℕ) (hend : 2 * endpoint < n) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶ Frequency.partialSum n endpoint) =
      if frequency ≤ endpoint then 1 else 0 := by
  let : Simple (frequencyFDRep n frequency) :=
    frequencyFDRep_simple_of_lower_half n frequency hpositive hbelow
  induction endpoint with
  | zero =>
      rw [Frequency.partialSum_zero]
      let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
        apply (FDRep.simple_iff_isIrreducible _).mpr
        change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
        infer_instance
      rw [frequency_hom_scalar frequency hpositive hbelow _ (by
        change Module.finrank ℂ ℂ = 1
        simp)]
      simp [Nat.not_le.mpr hpositive]
  | succ endpoint hinduction =>
      rw [Frequency.partialSum_succ, hom_biprod_finrank,
        hinduction (by omega)]
      let : Simple (frequencyFDRep n (endpoint + 1 : ℕ)) :=
        frequencyFDRep_simple_of_lower_half n (endpoint + 1) (by omega) hend
      rw [FDRep.finrank_hom_simple_simple,
        frequencyFDRep_iso_iff_frequency_eq n frequency (endpoint + 1) hbelow hend]
      split_ifs <;> omega

/-- Distinct positive lower-half frequencies have orthogonal morphism spaces. -/
theorem frequency_hom_frequency (first second : ℕ)
    (hfirst : 0 < first) (hsecond : 0 < second)
    (hfirstBelow : 2 * first < n) (hsecondBelow : 2 * second < n) :
    Module.finrank ℂ (frequencyFDRep n first ⟶ frequencyFDRep n second) =
      if first = second then 1 else 0 := by
  let : Simple (frequencyFDRep n first) :=
    frequencyFDRep_simple_of_lower_half n first hfirst hfirstBelow
  let : Simple (frequencyFDRep n second) :=
    frequencyFDRep_simple_of_lower_half n second hsecond hsecondBelow
  rw [FDRep.finrank_hom_simple_simple,
    frequencyFDRep_iso_iff_frequency_eq n first second hfirstBelow hsecondBelow]
  split_ifs <;> rfl

/-- Every reflection-coset object contains each positive lower-half frequency once. -/
theorem frequency_hom_coset (frequency : ℕ) (hpositive : 0 < frequency)
    (hbelow : 2 * frequency < n) (alpha : PositiveRoot n) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶ alpha.cosetFDRep) = 1 := by
  by_cases heven : Even n
  · obtain ⟨equivalence⟩ := alpha.coset_even_iso heven
    rw [hom_iso_finrank _ equivalence, hom_biprod_finrank]
    let : Simple (alpha.scalarFDRep heven) := evenScalarFDRep_simple n heven _
    rw [frequency_hom_scalar frequency hpositive hbelow (alpha.scalarFDRep heven)
        (evenScalarFDRep_finrank n heven _),
      frequency_hom_prefix frequency hpositive hbelow (n / 2 - 1) (by omega)]
    have hbound : frequency ≤ n / 2 - 1 := by
      obtain ⟨half, hhalf⟩ := heven
      omega
    simp only [hbound, ite_true, zero_add]
  · obtain ⟨equivalence⟩ := alpha.coset_odd_iso (Nat.not_even_iff_odd.mp heven)
    rw [hom_iso_finrank _ equivalence,
      frequency_hom_prefix frequency hpositive hbelow ((n - 1) / 2) (by
        obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
        omega)]
    have hbound : frequency ≤ (n - 1) / 2 := by omega
    simp only [hbound, ite_true]

/-- Two reflection-coset objects contain two copies of every lower-half frequency. -/
theorem frequency_hom_coset_pair (frequency : ℕ) (hpositive : 0 < frequency)
    (hbelow : 2 * frequency < n) (first second : PositiveRoot n) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶ first.cosetFDRep ⊞ second.cosetFDRep) =
      2 := by
  rw [hom_biprod_finrank, frequency_hom_coset frequency hpositive hbelow,
    frequency_hom_coset frequency hpositive hbelow]


end Schubert.Dihedral
