import Schubert.DihedralSplines.HessenbergClassification
import Schubert.DihedralSplines.HessenbergFamilies
import Mathlib.SetTheory.Cardinal.Finite

/-! # Counting Hessenberg ideals

The two classified families are disjoint and have n minus one and floor(n/2)
minus one members. Their parameterization counts ideals without choosing a
substitute root order.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

/-- There are n plus floor(n/2) minus two Hessenberg ideals containing the simple roots. -/
theorem natCard (n : ℕ) (hthree : 3 ≤ n) :
    Nat.card (HessenbergSpace n hthree) = n + n / 2 - 2 := by
  classical
  let build : Fin (n - 1) ⊕ Fin (n / 2 - 1) → HessenbergSpace n hthree := fun parameter =>
    match parameter with
    | .inl initial => Classical.choose (exists_initial_segment n hthree (initial.val + 2)
        (by omega) (by have := initial.isLt; omega))
    | .inr other => Classical.choose (exists_other_root_final_layer n hthree (other.val + 2)
        (by omega) (by have := other.isLt; omega))
  have hleft (parameter : Fin (n - 1)) :
      (build (.inl parameter)).roots.card = parameter.val + 2 ∧
        ∀ index : PositiveRootIndex n, index ∈ (build (.inl parameter)).roots ↔
          index.val < parameter.val + 2 :=
    Classical.choose_spec (exists_initial_segment n hthree (parameter.val + 2)
      (by omega) (by have := parameter.isLt; omega))
  have hright (parameter : Fin (n / 2 - 1)) :
      (build (.inr parameter)).roots.card = 2 * (parameter.val + 2) - 1 ∧
        ∀ index : PositiveRootIndex n, index ∈ (build (.inr parameter)).roots ↔
          index.val < 2 * (parameter.val + 2) - 2 ∨
            index.val = 2 * (parameter.val + 2) - 1 :=
    Classical.choose_spec (exists_other_root_final_layer n hthree (parameter.val + 2)
      (by omega) (by have := parameter.isLt; omega))
  have hdisjoint (initial : Fin (n - 1)) (other : Fin (n / 2 - 1)) :
      build (.inl initial) ≠ build (.inr other) := by
    intro heq
    have hcard := congrArg (fun ideal : HessenbergSpace n hthree => ideal.roots.card) heq
    rw [(hleft initial).1, (hright other).1] at hcard
    have hbound : 2 * (other.val + 2) - 1 < n := by have := other.isLt; omega
    let last : PositiveRootIndex n := ⟨2 * (other.val + 2) - 1, hbound⟩
    have hmem : last ∈ (build (.inr other)).roots :=
      (hright other).2 last |>.mpr (Or.inr rfl)
    rw [← heq] at hmem
    have hlt := (hleft initial).2 last |>.mp hmem
    change 2 * (other.val + 2) - 1 < initial.val + 2 at hlt
    omega
  have hinjective : Function.Injective build := by
    intro first second heq
    cases first with
    | inl first =>
      cases second with
      | inl second =>
        have hcard := congrArg (fun ideal : HessenbergSpace n hthree => ideal.roots.card) heq
        rw [(hleft first).1, (hleft second).1] at hcard
        have hvalue : first.val = second.val := by omega
        exact congrArg Sum.inl (Fin.ext hvalue)
      | inr second => exact (hdisjoint first second heq).elim
    | inr first =>
      cases second with
      | inl second => exact (hdisjoint second first heq.symm).elim
      | inr second =>
        have hcard := congrArg (fun ideal : HessenbergSpace n hthree => ideal.roots.card) heq
        rw [(hright first).1, (hright second).1] at hcard
        have hvalue : first.val = second.val := by omega
        exact congrArg Sum.inr (Fin.ext hvalue)
  have hsurjective : Function.Surjective build := by
    intro ideal
    rcases ideal.paper_family_classification with ⟨size, htwo, hbound, hmembership⟩ |
      ⟨layer, htwo, hbound, hmembership⟩
    · let parameter : Fin (n - 1) := ⟨size - 2, by omega⟩
      refine ⟨.inl parameter, ?_⟩
      apply HessenbergSpace.ext
      ext index
      rw [(hleft parameter).2, hmembership]
      have hvalue : parameter.val + 2 = size := by dsimp [parameter]; omega
      rw [hvalue]
    · let parameter : Fin (n / 2 - 1) := ⟨layer - 2, by omega⟩
      refine ⟨.inr parameter, ?_⟩
      apply HessenbergSpace.ext
      ext index
      rw [(hright parameter).2, hmembership]
      have hvalue : parameter.val + 2 = layer := by dsimp [parameter]; omega
      rw [hvalue]
  have hequivalence := Equiv.ofBijective build ⟨hinjective, hsurjective⟩
  rw [← Nat.card_congr hequivalence, Nat.card_sum, Nat.card_fin, Nat.card_fin]
  omega

end Schubert.DihedralSplines.HessenbergSpace
