import DihedralHessenberg.Dihedral.CosetFDRep
import DihedralHessenberg.Dihedral.RootScalarCharacter
import DihedralHessenberg.Dihedral.FrequencySum
import DihedralHessenberg.Dihedral.FrequencyFourier
import DihedralHessenberg.FiniteGroupCharacters.FrequencyPairs
import TauCeti.RepresentationTheory.RepresentationRing.Injective

/-! # Irreducible decompositions of root-reflection coset representations -/

noncomputable section

open CategoryTheory Limits
open scoped BigOperators

namespace Schubert.Dihedral.Frequency

/-- The lower-half prefix and even midpoint exhaust the cyclic rotation trace. -/
theorem partialSum_rotation_total (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    (partialSum n ((n - 1) / 2)).character (.r coordinate) +
      (if Even n then (-1 : ℂ) ^ coordinate.val else 0) =
        if coordinate = 0 then (n : ℂ) else 0 := by
  classical
  have hpairs := Schubert.FiniteGroupCharacters.sum_frequency_pairs
    (fun frequency : ZMod n => ZMod.stdAddChar (frequency * coordinate))
  have htotal : ∑ frequency : ZMod n, ZMod.stdAddChar (frequency * coordinate) =
      if coordinate = 0 then (n : ℂ) else 0 := by
    simpa only [mul_comm] using additive_sum n coordinate
  rw [htotal] at hpairs
  simp only [zero_mul, AddChar.map_zero_eq_one, neg_mul] at hpairs
  have hfrequencies :
      ∑ index : Fin ((n - 1) / 2),
        (ZMod.stdAddChar (((index.val + 1 : ℕ) : ZMod n) * coordinate) +
          ZMod.stdAddChar (-(((index.val + 1 : ℕ) : ZMod n) * coordinate))) =
        ∑ index ∈ Finset.range ((n - 1) / 2),
          (frequencyFDRep n (index + 1 : ℕ)).character (.r coordinate) := by
    rw [Fin.sum_univ_eq_sum_range (fun index : ℕ =>
      ZMod.stdAddChar (((index + 1 : ℕ) : ZMod n) * coordinate) +
        ZMod.stdAddChar (-(((index + 1 : ℕ) : ZMod n) * coordinate))) ((n - 1) / 2)]
    apply Finset.sum_congr rfl
    intro index _
    rw [character_additive]
  rw [hfrequencies] at hpairs
  rw [partialSum_character]
  by_cases heven : Even n
  · rw [ite_eq_left heven, additive_midpoint_mul n heven] at hpairs
    rw [ite_eq_left heven]
    exact hpairs.symm
  · rw [ite_eq_right heven] at hpairs ⊢
    exact hpairs.symm

end Schubert.Dihedral.Frequency

namespace Schubert.Dihedral.PositiveRoot

/-- The coset rotation character is the cyclic identity indicator. -/
theorem cosetFDRep_character_r {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (coordinate : ZMod n) :
    alpha.cosetFDRep.character (.r coordinate) =
      if coordinate = 0 then (n : ℂ) else 0 := by
  rw [cosetFDRep_character]
  by_cases hzero : coordinate = 0
  · subst coordinate
    simpa only [DihedralGroup.r_zero, ite_true] using alpha.coset_character_one
  · rw [ite_eq_right hzero]
    exact alpha.coset_character_rotation coordinate hzero

/-- For odd rotation order, the root coset object is the complete lower-half prefix. -/
theorem coset_odd_iso {n : ℕ} [NeZero n] (alpha : PositiveRoot n) (hodd : Odd n) :
    Nonempty (alpha.cosetFDRep ≅ Frequency.partialSum n ((n - 1) / 2)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  cases element with
  | r coordinate =>
      rw [cosetFDRep_character_r]
      have htrace := Frequency.partialSum_rotation_total n coordinate
      have hnotEven := Nat.not_even_iff_odd.mpr hodd
      simpa only [hnotEven, ite_false, add_zero] using htrace.symm
  | sr coordinate =>
      rw [cosetFDRep_character, coset_character_odd alpha hodd,
        Frequency.partialSum_character_sr]

/-- For even rotation order, the coset object adds its unique fixed-root scalar character. -/
theorem coset_even_iso {n : ℕ} [NeZero n] (alpha : PositiveRoot n) (heven : Even n) :
    Nonempty (alpha.cosetFDRep ≅
      (alpha.scalarFDRep heven ⊞ Frequency.partialSum n (n / 2 - 1))) := by
  have hhalf : (n - 1) / 2 = n / 2 - 1 := by
    have hpositive := NeZero.pos n
    obtain ⟨half, hhalf⟩ := heven
    omega
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  cases element with
  | r coordinate =>
      rw [cosetFDRep_character_r, FDRep.char_biprod, Pi.add_apply, scalarFDRep,
        evenScalarFDRep_character, evenScalarCharacter_r, ← neg_one_pow_eq_pow_mod_two]
      have htrace := Frequency.partialSum_rotation_total n coordinate
      rw [ite_eq_left heven, hhalf] at htrace
      simpa only [add_comm] using htrace.symm
  | sr coordinate =>
      rw [cosetFDRep_character, coset_character_even alpha heven, FDRep.char_biprod,
        Pi.add_apply, Frequency.partialSum_character_sr, scalarFDRep, evenScalarFDRep_character]
      change (if IsConj (DihedralGroup.sr coordinate) alpha.reflection then 2 else 0) =
        alpha.scalarCharacter heven (.sr coordinate) + 1
      rw [scalarCharacter_sr]
      split_ifs <;> norm_num

/-- The odd coset decomposition is an equality in the representation ring. -/
theorem coset_odd_class {n : ℕ} [NeZero n] (alpha : PositiveRoot n) (hodd : Odd n) :
    (TauCeti.SplitK0.of alpha.cosetFDRep : TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (Frequency.partialSum n ((n - 1) / 2)) := by
  obtain ⟨isomorphism⟩ := alpha.coset_odd_iso hodd
  exact TauCeti.SplitK0.of_congr isomorphism

/-- The even coset decomposition is an equality in the representation ring. -/
theorem coset_even_class {n : ℕ} [NeZero n] (alpha : PositiveRoot n) (heven : Even n) :
    (TauCeti.SplitK0.of alpha.cosetFDRep : TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (alpha.scalarFDRep heven) +
        TauCeti.SplitK0.of (Frequency.partialSum n (n / 2 - 1)) := by
  obtain ⟨isomorphism⟩ := alpha.coset_even_iso heven
  exact (TauCeti.SplitK0.of_congr isomorphism).trans (TauCeti.SplitK0.of_biprod _ _)

end Schubert.Dihedral.PositiveRoot
