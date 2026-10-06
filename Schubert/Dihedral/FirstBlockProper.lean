import Schubert.Dihedral.CyclicProperIntervals
import Schubert.Dihedral.CyclicBlockForms
import Schubert.Dihedral.BlockTranslation

/-! # The reflection stabilizing a first-orientation alternating block -/

namespace Schubert.Dihedral

/-- The first alternating block is stabilized exactly by identity and its terminal reflection. -/
theorem first_block_stabilizer_proper {n : ℕ} {hthree : 3 ≤ n} (half : ℕ)
    (hbound : 2 * half < n) (element : DihedralGroup n) :
    (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half).image
      (fun current => element * current) =
        alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half ↔
      element = 1 ∨ element = (positiveRootEquiv n ⟨2 * half, by omega⟩).reflection := by
  classical
  let gamma : PositiveRoot n := positiveRootEquiv n ⟨2 * half, by omega⟩
  let terminal := (simpleRoot n hthree 0).alternatingProduct (simpleRoot n hthree 1)
    (2 * half + 1)
  have hterminal : gamma.reflection = terminal := by
    dsimp only [gamma, terminal]
    rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
      simpleReflection_zero, simpleReflection_one]
    exact numbered_even_reflection n half (by omega)
  have hzero : Cyclic.vertex n hthree ⟨0, by omega⟩ = 1 := by
    rw [Cyclic.vertex, PositiveRoot.alternating_zero]
  have hbase := (Cyclic.interval_even (n := n) (hthree := hthree)
    ⟨0, by omega⟩ half (by simp)).symm
  rw [hzero] at hbase
  rw [← alternatingBlock_translate, mul_one]
  constructor
  · intro heq
    obtain ⟨start, hstart⟩ := Cyclic.surjective (n := n) (hthree := hthree) element
    by_cases heven : Even start.val
    · have hinterval := (Cyclic.interval_even (hthree := hthree) start half heven).symm
      rw [hstart, heq, hbase] at hinterval
      have hstartZero := Cyclic.proper_interval_injective (2 * half + 2) (by omega) (by omega)
        hinterval
      left
      rw [← hstart, ← hstartZero, hzero]
    · obtain ⟨finish, hfinish⟩ := Cyclic.surjective (n := n) (hthree := hthree)
        (element * terminal)
      have hparity := Cyclic.reflection_parity start finish gamma (by
        rw [hstart, hfinish, hterminal])
      have hfinishEven : Even finish.val := by tauto
      have hinterval := (Cyclic.interval_even (hthree := hthree) finish half hfinishEven).symm
      rw [hfinish, alternatingBlock_reverse, heq, hbase] at hinterval
      have hfinishZero := Cyclic.proper_interval_injective (2 * half + 2) (by omega) (by omega)
        hinterval
      have hfinishOne : element * terminal = 1 := by
        rw [← hfinish, ← hfinishZero, hzero]
      right
      have hproduct := congrArg (fun value => value * terminal) hfinishOne
      rw [mul_assoc, ← hterminal, gamma.reflection_square, mul_one, one_mul] at hproduct
      exact hproduct
  · rintro (rfl | helement)
    · rfl
    · change element = gamma.reflection at helement
      rw [helement, hterminal]
      simpa only [one_mul] using alternatingBlock_reverse (1 : DihedralGroup n)
        (simpleRoot n hthree 0) (simpleRoot n hthree 1) half

end Schubert.Dihedral
