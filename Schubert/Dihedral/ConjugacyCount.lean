import Schubert.Dihedral.CommutingCoordinates
import Mathlib.GroupTheory.GroupAction.CardCommute

/-! # Number of conjugacy classes for even dihedral groups -/

namespace Schubert.Dihedral

private def commutingPairCoordinateEquiv (n : ℕ) :
    {pair : DihedralGroup n × DihedralGroup n // Commute pair.1 pair.2} ≃
      (ZMod n × ZMod n) ⊕
        ({coordinate : ZMod n // coordinate + coordinate = 0} × ZMod n) ⊕
        (ZMod n × {coordinate : ZMod n // coordinate + coordinate = 0}) ⊕
        (ZMod n × {coordinate : ZMod n // coordinate + coordinate = 0}) where
  toFun := fun
    | ⟨⟨.r first, .r second⟩, _⟩ => .inl (first, second)
    | ⟨⟨.r first, .sr second⟩, h⟩ =>
      .inr (.inl (⟨first, (commute_r_sr_iff n first second).mp h⟩, second))
    | ⟨⟨.sr first, .r second⟩, h⟩ =>
      .inr (.inr (.inl (first, ⟨second, (commute_sr_r_iff n first second).mp h⟩)))
    | ⟨⟨.sr first, .sr second⟩, h⟩ =>
      .inr (.inr (.inr (first, ⟨second - first, (commute_sr_sr_iff n first second).mp h⟩)))
  invFun := fun
    | .inl (first, second) =>
      ⟨⟨.r first, .r second⟩, by
        change DihedralGroup.r (first + second) = DihedralGroup.r (second + first)
        rw [add_comm]⟩
    | .inr (.inl (first, second)) =>
      ⟨⟨.r first.val, .sr second⟩, (commute_r_sr_iff n first.val second).mpr first.property⟩
    | .inr (.inr (.inl (first, second))) =>
      ⟨⟨.sr first, .r second.val⟩, (commute_sr_r_iff n first second.val).mpr second.property⟩
    | .inr (.inr (.inr (first, second))) =>
      ⟨⟨.sr first, .sr (first + second.val)⟩,
        (commute_sr_sr_iff n first (first + second.val)).mpr
          (by simpa [add_comm] using second.property)⟩
  left_inv := by
    rintro ⟨⟨first, second⟩, h⟩
    cases first <;> cases second <;> apply Subtype.ext <;> simp
  right_inv := fun
    | .inl (_, _) => rfl
    | .inr (.inl (_, _)) => rfl
    | .inr (.inr (.inl (_, _))) => rfl
    | .inr (.inr (.inr (first, second))) => by
      apply congrArg Sum.inr
      apply congrArg Sum.inr
      apply congrArg Sum.inr
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp

/-- A positive even dihedral group has n(n+6) ordered commuting pairs. -/
theorem card_commuting_pairs_of_even (n : ℕ) [NeZero n] (heven : Even n) :
    Nat.card {pair : DihedralGroup n × DihedralGroup n // Commute pair.1 pair.2} =
      n * (n + 6) := by
  rw [Nat.card_congr (commutingPairCoordinateEquiv n)]
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_zmod, card_add_self_eq_zero_of_even n heven]
  ring

/-- A positive even dihedral group has (n+6)/2 conjugacy classes. -/
theorem card_conjClasses_of_even (n : ℕ) [NeZero n] (heven : Even n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 6) / 2 := by
  have hnpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← Nat.mul_div_mul_left _ 2 hnpositive, ← card_commuting_pairs_of_even n heven,
    mul_comm, card_comm_eq_card_conjClasses_mul_card, DihedralGroup.nat_card,
    Nat.mul_div_left _ (mul_pos two_pos hnpositive)]

/-- The conjugacy-class count is (n+6)/2 for even n and (n+3)/2 for odd n. -/
theorem card_conjClasses_piecewise (n : ℕ) [NeZero n] :
    Nat.card (ConjClasses (DihedralGroup n)) = if Even n then (n + 6) / 2 else (n + 3) / 2 := by
  by_cases heven : Even n
  · rw [ite_eq_left heven]
    exact card_conjClasses_of_even n heven
  · rw [ite_eq_right heven]
    exact DihedralGroup.card_conjClasses_odd (Nat.not_even_iff_odd.mp heven)
end Schubert.Dihedral
