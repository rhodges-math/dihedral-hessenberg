import Schubert.Dihedral.Group
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Ring

/-! # Conjugacy of concrete dihedral rotations and reflections -/

namespace Schubert.Dihedral

/-- Two rotations are conjugate precisely when their coordinates agree up to sign. -/
theorem isConj_r_iff (n : ℕ) (first second : ZMod n) :
    IsConj (DihedralGroup.r first) (DihedralGroup.r second) ↔
      second = first ∨ second = -first := by
  rw [isConj_iff]
  constructor
  · rintro ⟨element, heq⟩
    cases element with
    | r coordinate =>
      simp only [DihedralGroup.inv_r, DihedralGroup.r_mul_r, DihedralGroup.r.injEq] at heq
      exact Or.inl (by simpa [add_comm, add_left_comm, add_assoc] using heq.symm)
    | sr coordinate =>
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, DihedralGroup.r.injEq] at heq
      exact Or.inr (by simpa [sub_eq_add_neg, add_assoc] using heq.symm)
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨DihedralGroup.sr 0, by simp⟩

/-- A rotation is never conjugate to a reflection. -/
theorem not_isConj_r_sr (n : ℕ) (first second : ZMod n) :
    ¬IsConj (DihedralGroup.r first) (DihedralGroup.sr second) := by
  rw [isConj_iff]
  rintro ⟨element, heq⟩
  cases element <;> simp [DihedralGroup.inv_r, DihedralGroup.inv_sr,
    DihedralGroup.r_mul_r, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] at heq

/-- Two reflections are conjugate precisely when their difference is twice a coordinate. -/
theorem isConj_sr_iff (n : ℕ) (first second : ZMod n) :
    IsConj (DihedralGroup.sr first) (DihedralGroup.sr second) ↔
      ∃ coordinate : ZMod n, 2 * coordinate = second - first := by
  rw [isConj_iff]
  constructor
  · rintro ⟨element, heq⟩
    cases element with
    | r coordinate =>
      simp only [DihedralGroup.inv_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq] at heq
      refine ⟨-coordinate, ?_⟩
      rw [← heq]
      ring
    | sr coordinate =>
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
        DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq] at heq
      refine ⟨coordinate - first, ?_⟩
      rw [← heq]
      ring
  · rintro ⟨coordinate, hdouble⟩
    refine ⟨DihedralGroup.r (-coordinate), ?_⟩
    simp only [DihedralGroup.inv_r, neg_neg, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq]
    calc
      first - -coordinate + coordinate = first + 2 * coordinate := by ring
      _ = second := by rw [hdouble]; ring

/-- For odd polygon parameter, every two reflections are conjugate. -/
theorem isConj_sr_of_odd (n : ℕ) (hodd : Odd n) (first second : ZMod n) :
    IsConj (DihedralGroup.sr first) (DihedralGroup.sr second) := by
  have hcoprime : Nat.Coprime 2 n :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat
  let unit := ZMod.unitOfCoprime 2 hcoprime
  have hcoe : (unit : ZMod n) = 2 := ZMod.coe_unitOfCoprime 2 hcoprime
  apply (isConj_sr_iff n first second).mpr
  refine ⟨(unit⁻¹ : ZMod n) * (second - first), ?_⟩
  rw [← hcoe]
  exact unit.mul_inv_cancel_left _

private theorem exists_double_iff_val_parity (n : ℕ) [NeZero n] (heven : Even n)
    (first second : ZMod n) :
    (∃ coordinate : ZMod n, 2 * coordinate = second - first) ↔
      first.val % 2 = second.val % 2 := by
  constructor
  · rintro ⟨coordinate, hdouble⟩
    have hadd : first + 2 * coordinate = second := by rw [hdouble]; ring
    have hcast : ((first.val + 2 * coordinate.val : ℕ) : ZMod n) = (second.val : ZMod n) := by
      push_cast
      simpa only [ZMod.natCast_zmod_val] using hadd
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ n).mp hcast
    have hdiv : 2 ∣ n := by
      obtain ⟨half, hhalf⟩ := heven
      exact ⟨half, by omega⟩
    have hparity := hmod.of_dvd hdiv
    simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod] using hparity
  · intro hparity
    let difference := second.val + n - first.val
    have hfirst := ZMod.val_lt first
    have hsum : first.val + difference = second.val + n := by dsimp [difference]; omega
    have hnmod := Nat.even_iff.mp heven
    have hmod : difference % 2 = 0 := by omega
    have hdouble : 2 * (difference / 2) = difference := by omega
    have hcast := congrArg (fun value : ℕ => (value : ZMod n)) hdouble
    push_cast at hcast
    have hsumCast := congrArg (fun value : ℕ => (value : ZMod n)) hsum
    push_cast at hsumCast
    simp only [ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero] at hsumCast
    refine ⟨(difference / 2 : ℕ), ?_⟩
    rw [hcast, ← hsumCast]
    ring

/-- For even polygon parameter, reflection conjugacy is equality of coordinate parity. -/
theorem isConj_sr_iff_val_parity_of_even (n : ℕ) [NeZero n] (heven : Even n)
    (first second : ZMod n) :
    IsConj (DihedralGroup.sr first) (DihedralGroup.sr second) ↔
      first.val % 2 = second.val % 2 := by
  rw [isConj_sr_iff, exists_double_iff_val_parity n heven]
end Schubert.Dihedral
