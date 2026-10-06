import Schubert.Dihedral.CyclicBlockForms
import Schubert.Dihedral.BlockTranslation

/-! # The reflection stabilizing a second-orientation alternating block -/

namespace Schubert.Dihedral

/-- The second alternating block is stabilized exactly by identity and its terminal reflection. -/
theorem second_block_stabilizer {n : ℕ} {hthree : 3 ≤ n} (half : ℕ)
    (hbound : 2 * half + 1 < n) (element : DihedralGroup n) :
    (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half).image
      (fun current => element * current) =
        alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half ↔
      element = 1 ∨ element = (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection := by
  classical
  let gamma : PositiveRoot n := positiveRootEquiv n ⟨2 * half + 1, hbound⟩
  let terminal := (simpleRoot n hthree 1).alternatingProduct (simpleRoot n hthree 0)
    (2 * half + 1)
  have hterminal : gamma.reflection = terminal := by
    dsimp only [gamma, terminal]
    rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
      simpleReflection_one, simpleReflection_zero]
    exact numbered_odd_reflection n half hbound
  have hzero : Cyclic.vertex n hthree ⟨0, by omega⟩ = 1 := by
    rw [Cyclic.vertex, PositiveRoot.alternating_zero]
  obtain ⟨baseline, hbaseline⟩ := Cyclic.surjective (n := n) (hthree := hthree) terminal
  have hbaselineParity := Cyclic.reflection_parity ⟨0, by omega⟩ baseline gamma (by
    rw [hzero, hbaseline, hterminal, one_mul])
  have hbaselineOdd : ¬Even baseline.val := by simpa using hbaselineParity.mp (by simp)
  have hbase := (Cyclic.interval_odd (hthree := hthree) baseline half hbaselineOdd).symm
  rw [hbaseline] at hbase
  have hreverse := alternatingBlock_reverse (1 : DihedralGroup n)
    (simpleRoot n hthree 1) (simpleRoot n hthree 0) half
  simp only [one_mul] at hreverse
  rw [hreverse] at hbase
  rw [← alternatingBlock_translate, mul_one]
  constructor
  · intro heq
    obtain ⟨start, hstart⟩ := Cyclic.surjective (n := n) (hthree := hthree) element
    by_cases hodd : ¬Even start.val
    · have hinterval := (Cyclic.interval_odd (hthree := hthree) start half hodd).symm
      rw [hstart, heq, hbase] at hinterval
      have hstartEq := Cyclic.interval_injective (2 * half + 2) (by omega) (by omega)
        hinterval
      right
      rw [← hstart, ← hstartEq, hbaseline, ← hterminal]
    · obtain ⟨finish, hfinish⟩ := Cyclic.surjective (n := n) (hthree := hthree)
        (element * terminal)
      have hparity := Cyclic.reflection_parity start finish gamma (by
        rw [hstart, hfinish, hterminal])
      have hfinishOdd : ¬Even finish.val := by tauto
      have hinterval := (Cyclic.interval_odd (hthree := hthree) finish half hfinishOdd).symm
      rw [hfinish, alternatingBlock_reverse, heq, hbase] at hinterval
      have hfinishEq := Cyclic.interval_injective (2 * half + 2) (by omega) (by omega)
        hinterval
      have hproductEq : element * terminal = terminal := by
        rw [← hfinish, ← hfinishEq, hbaseline]
      left
      have hproduct := congrArg (fun value => value * terminal) hproductEq
      simpa only [← hterminal, mul_assoc, gamma.reflection_square, mul_one] using hproduct
  · rintro (rfl | helement)
    · rfl
    · change element = gamma.reflection at helement
      rw [helement, hterminal]
      simpa only [one_mul] using alternatingBlock_reverse (1 : DihedralGroup n)
        (simpleRoot n hthree 1) (simpleRoot n hthree 0) half

end Schubert.Dihedral
