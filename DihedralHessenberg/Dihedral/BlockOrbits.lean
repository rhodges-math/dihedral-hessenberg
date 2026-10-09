import DihedralHessenberg.Dihedral.BlockCosetOrbit
import DihedralHessenberg.Dihedral.CyclicBlockForms

/-! # Two disjoint standard orbits of alternating blocks -/

namespace Schubert.Dihedral

open scoped Pointwise

/-- The standard orbit is exactly the family of blocks with all possible bases. -/
theorem alternatingBlock_orbit {n : ℕ} (alpha beta : PositiveRoot n) (half : ℕ) :
    MulAction.orbit (DihedralGroup n) (alternatingBlock 1 alpha beta half) =
      {block : Finset (DihedralGroup n) |
        ∃ base, block = alternatingBlock base alpha beta half} := by
  ext block
  change (∃ element : DihedralGroup n, element • alternatingBlock 1 alpha beta half = block) ↔ _
  constructor
  · rintro ⟨element, rfl⟩
    refine ⟨element, ?_⟩
    simpa only [Finset.smul_finset_def, smul_eq_mul, mul_one] using
      (alternatingBlock_translate element 1 alpha beta half).symm
  · rintro ⟨element, rfl⟩
    refine ⟨element, ?_⟩
    simpa only [Finset.smul_finset_def, smul_eq_mul, mul_one] using
      (alternatingBlock_translate element 1 alpha beta half).symm

/-- The two simple-root block orientations have disjoint vertex-set orbits. -/
theorem block_orbits_disjoint {n : ℕ} {hthree : 3 ≤ n} (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    Disjoint
      (MulAction.orbit (DihedralGroup n)
        (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half))
      (MulAction.orbit (DihedralGroup n)
        (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half)) := by
  rw [alternatingBlock_orbit, alternatingBlock_orbit]
  apply Set.disjoint_left.mpr
  rintro block ⟨first, hfirst⟩ ⟨second, hsecond⟩
  obtain ⟨start, heven, hstart⟩ := Cyclic.first_interval (hthree := hthree) first half hbound
  obtain ⟨finish, hodd, hfinish⟩ := Cyclic.second_interval (hthree := hthree) second half hbound
  have hinterval : Cyclic.interval n hthree start (2 * half + 2) =
      Cyclic.interval n hthree finish (2 * half + 2) := by
    rw [← hstart, ← hfinish, ← hfirst, ← hsecond]
  have heq := Cyclic.interval_injective (2 * half + 2) (by omega) (by omega) hinterval
  exact hodd (heq ▸ heven)

/-- Each first-orientation block orbit has exactly n vertex sets. -/
theorem card_first_block_orbit {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    Nat.card (MulAction.orbit (DihedralGroup n)
      (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half)) = n := by
  obtain ⟨equivalence, _⟩ := first_block_cosets (hthree := hthree) half hbound
  rw [← Nat.card_congr equivalence]
  exact PositiveRoot.card_cosets _

/-- Each second-orientation block orbit has exactly n vertex sets. -/
theorem card_second_block_orbit {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    Nat.card (MulAction.orbit (DihedralGroup n)
      (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half)) = n := by
  obtain ⟨equivalence, _⟩ := second_block_cosets (hthree := hthree) half hbound
  rw [← Nat.card_congr equivalence]
  exact PositiveRoot.card_cosets _

end Schubert.Dihedral
