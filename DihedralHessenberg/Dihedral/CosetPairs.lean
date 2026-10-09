import DihedralHessenberg.Dihedral.CosetDecomposition

/-! # Pairs of nonconjugate reflection-coset representations -/

noncomputable section

open CategoryTheory Limits

namespace Schubert.Dihedral.PositiveRoot

/-- Two nonconjugate reflection-coset objects have total reflection trace two. -/
theorem coset_pair_sr {n : ℕ} [NeZero n] (first second : PositiveRoot n) (heven : Even n)
    (hnonconj : ¬ IsConj first.reflection second.reflection) (coordinate : ZMod n) :
    first.cosetFDRep.character (.sr coordinate) + second.cosetFDRep.character (.sr coordinate) =
      2 := by
  have hparity : (reflectionCoordinate first.index).val % 2 ≠
      (reflectionCoordinate second.index).val % 2 := by
    change ¬ IsConj (rootReflection first.index) (rootReflection second.index) at hnonconj
    rwa [rootReflection_eq_sr, rootReflection_eq_sr,
      isConj_sr_iff_val_parity_of_even n heven] at hnonconj
  rw [cosetFDRep_character, cosetFDRep_character,
    coset_character_even first heven, coset_character_even second heven]
  change (if IsConj (DihedralGroup.sr coordinate) (rootReflection first.index) then 2 else 0) +
    (if IsConj (DihedralGroup.sr coordinate) (rootReflection second.index) then 2 else 0) = 2
  simp only [rootReflection_eq_sr, isConj_sr_iff_val_parity_of_even n heven]
  have hcoordinate := Nat.mod_lt coordinate.val (by decide : 0 < 2)
  have hfirst := Nat.mod_lt (reflectionCoordinate first.index).val (by decide : 0 < 2)
  have hsecond := Nat.mod_lt (reflectionCoordinate second.index).val (by decide : 0 < 2)
  by_cases hmatch : coordinate.val % 2 = (reflectionCoordinate first.index).val % 2
  · have hother : coordinate.val % 2 ≠ (reflectionCoordinate second.index).val % 2 := by omega
    rw [ite_eq_left hmatch, ite_eq_right hother, add_zero]
  · have hother : coordinate.val % 2 = (reflectionCoordinate second.index).val % 2 := by omega
    rw [ite_eq_right hmatch, ite_eq_left hother, zero_add]

/-- Every pair representing the two reflection classes gives the same coset biproduct. -/
theorem opposite_pairs_iso {n : ℕ} [NeZero n] (first second third fourth : PositiveRoot n)
    (heven : Even n) (hfirst : ¬ IsConj first.reflection second.reflection)
    (hsecond : ¬ IsConj third.reflection fourth.reflection) :
    Nonempty ((first.cosetFDRep ⊞ second.cosetFDRep) ≅
      (third.cosetFDRep ⊞ fourth.cosetFDRep)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  simp only [FDRep.char_biprod, Pi.add_apply]
  cases element with
  | r coordinate => simp only [cosetFDRep_character_r]
  | sr coordinate =>
      rw [coset_pair_sr first second heven hfirst, coset_pair_sr third fourth heven hsecond]

/-- The exact two-class coset sum is independent of the choice of reflection representatives. -/
theorem opposite_pairs_class {n : ℕ} [NeZero n] (first second third fourth : PositiveRoot n)
    (heven : Even n) (hfirst : ¬ IsConj first.reflection second.reflection)
    (hsecond : ¬ IsConj third.reflection fourth.reflection) :
    (TauCeti.SplitK0.of first.cosetFDRep : TauCeti.repRing ℂ (DihedralGroup n)) +
      TauCeti.SplitK0.of second.cosetFDRep =
        TauCeti.SplitK0.of third.cosetFDRep + TauCeti.SplitK0.of fourth.cosetFDRep := by
  obtain ⟨isomorphism⟩ := opposite_pairs_iso first second third fourth heven hfirst hsecond
  simpa only [TauCeti.SplitK0.of_biprod] using TauCeti.SplitK0.of_congr isomorphism

end Schubert.Dihedral.PositiveRoot
