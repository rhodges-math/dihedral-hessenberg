import Schubert.Dihedral.FrequencyMultiplicity

/-! # Scalar constituents in frequency prefixes and coset objects -/

noncomputable section
open CategoryTheory
namespace Schubert.Dihedral
open Schubert.FiniteGroupCharacters
variable {n : ℕ} [NeZero n]

/-- Scalar objects have no morphisms into a lower-half frequency. -/
theorem scalar_hom_frequency (scalar : FDRep ℂ (DihedralGroup n)) [Simple scalar]
    (hdimension : Module.finrank ℂ scalar = 1) (frequency : ℕ)
    (hpositive : 0 < frequency) (hbelow : 2 * frequency < n) :
    Module.finrank ℂ (scalar ⟶ frequencyFDRep n frequency) = 0 := by
  let : Simple (frequencyFDRep n frequency) :=
    frequencyFDRep_simple_of_lower_half n frequency hpositive hbelow
  have hreverse := frequency_hom_scalar frequency hpositive hbelow scalar hdimension
  rw [FDRep.finrank_hom_simple_simple] at hreverse ⊢
  have hnot : ¬ Nonempty (frequencyFDRep n frequency ≅ scalar) := by
    intro hequal
    simp only [hequal, ite_true] at hreverse
    contradiction
  have hnotReverse : ¬ Nonempty (scalar ≅ frequencyFDRep n frequency) := by
    rintro ⟨equivalence⟩
    exact hnot ⟨equivalence.symm⟩
  simp only [hnotReverse, ite_false]

/-- A scalar sees only the trivial slot in a lower-half frequency prefix. -/
theorem scalar_hom_prefix (scalar : FDRep ℂ (DihedralGroup n)) [Simple scalar]
    (hdimension : Module.finrank ℂ scalar = 1) (endpoint : ℕ) (hend : 2 * endpoint < n) :
    Module.finrank ℂ (scalar ⟶ Frequency.partialSum n endpoint) =
      Module.finrank ℂ (scalar ⟶ FDRep.of
        (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  induction endpoint with
  | zero => rfl
  | succ endpoint induction =>
      rw [Frequency.partialSum, hom_biprod_finrank, induction (by omega),
        scalar_hom_frequency scalar hdimension (endpoint + 1) (by omega) hend, add_zero]

/-- Coset scalar multiplicities separate the trivial and reflection-selected slots. -/
theorem scalar_hom_coset (scalar : FDRep ℂ (DihedralGroup n)) [Simple scalar]
    (hdimension : Module.finrank ℂ scalar = 1) (alpha : PositiveRoot n) :
    Module.finrank ℂ (scalar ⟶ alpha.cosetFDRep) =
      Module.finrank ℂ (scalar ⟶ FDRep.of
        (Representation.trivial ℂ (DihedralGroup n) ℂ)) +
      if heven : Even n then Module.finrank ℂ (scalar ⟶ alpha.scalarFDRep heven) else 0 := by
  by_cases heven : Even n
  · obtain ⟨equivalence⟩ := alpha.coset_even_iso heven
    rw [hom_iso_finrank scalar equivalence, hom_biprod_finrank,
      scalar_hom_prefix scalar hdimension (n / 2 - 1) (by
        obtain ⟨half, hhalf⟩ := heven
        have hn := Nat.pos_of_ne_zero (NeZero.ne n)
        omega), dite_eq_left heven]
    exact add_comm _ _
  · obtain ⟨equivalence⟩ := alpha.coset_odd_iso (Nat.not_even_iff_odd.mp heven)
    rw [hom_iso_finrank scalar equivalence, scalar_hom_prefix scalar hdimension
      ((n - 1) / 2) (by
        obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
        omega), dite_eq_right heven, add_zero]

end Schubert.Dihedral
