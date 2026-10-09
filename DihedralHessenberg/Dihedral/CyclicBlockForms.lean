import DihedralHessenberg.Dihedral.CyclicIntervals
import DihedralHessenberg.Dihedral.CyclicParity
import DihedralHessenberg.Dihedral.BlockReversal
import DihedralHessenberg.Dihedral.RootNumbering

/-! # Cyclic interval forms of the two alternating block orientations -/

namespace Schubert.Dihedral.Cyclic

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Every first-root block is an interval beginning at an even cyclic position. -/
theorem first_interval (element : DihedralGroup n) (half : ℕ) (hbound : 2 * half + 1 < n) :
    ∃ start : Fin (2 * n), Even start.val ∧
      alternatingBlock element (simpleRoot n hthree 0) (simpleRoot n hthree 1) half =
        interval n hthree start (2 * half + 2) := by
  classical
  obtain ⟨start, hstart⟩ := surjective (n := n) (hthree := hthree) element
  by_cases heven : Even start.val
  · refine ⟨start, heven, ?_⟩
    rw [← hstart]
    exact (interval_even start half heven).symm
  · let terminal := (simpleRoot n hthree 0).alternatingProduct (simpleRoot n hthree 1)
      (2 * half + 1)
    let gamma : PositiveRoot n := positiveRootEquiv n ⟨2 * half, by omega⟩
    have hterminal : gamma.reflection = terminal := by
      dsimp only [gamma, terminal]
      rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
        simpleReflection_zero, simpleReflection_one]
      exact numbered_even_reflection n half (by omega)
    obtain ⟨finish, hfinish⟩ := surjective (n := n) (hthree := hthree) (element * terminal)
    have hparity := reflection_parity start finish gamma (by
      rw [hfinish, hstart, hterminal])
    have hfinishEven : Even finish.val := by tauto
    refine ⟨finish, hfinishEven, ?_⟩
    rw [← alternatingBlock_reverse element (simpleRoot n hthree 0)
      (simpleRoot n hthree 1) half]
    rw [← hfinish]
    exact (interval_even finish half hfinishEven).symm

/-- Every second-root block is an interval beginning at an odd cyclic position. -/
theorem second_interval (element : DihedralGroup n) (half : ℕ) (hbound : 2 * half + 1 < n) :
    ∃ start : Fin (2 * n), ¬Even start.val ∧
      alternatingBlock element (simpleRoot n hthree 1) (simpleRoot n hthree 0) half =
        interval n hthree start (2 * half + 2) := by
  classical
  obtain ⟨start, hstart⟩ := surjective (n := n) (hthree := hthree) element
  by_cases hodd : ¬Even start.val
  · refine ⟨start, hodd, ?_⟩
    rw [← hstart]
    exact (interval_odd start half hodd).symm
  · let terminal := (simpleRoot n hthree 1).alternatingProduct (simpleRoot n hthree 0)
      (2 * half + 1)
    let gamma : PositiveRoot n := positiveRootEquiv n ⟨2 * half + 1, hbound⟩
    have hterminal : gamma.reflection = terminal := by
      dsimp only [gamma, terminal]
      rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
        simpleReflection_one, simpleReflection_zero]
      exact numbered_odd_reflection n half hbound
    obtain ⟨finish, hfinish⟩ := surjective (n := n) (hthree := hthree) (element * terminal)
    have hparity := reflection_parity start finish gamma (by
      rw [hfinish, hstart, hterminal])
    have hfinishOdd : ¬Even finish.val := by tauto
    refine ⟨finish, hfinishOdd, ?_⟩
    rw [← alternatingBlock_reverse element (simpleRoot n hthree 1)
      (simpleRoot n hthree 0) half]
    rw [← hfinish]
    exact (interval_odd finish half hfinishOdd).symm

end Schubert.Dihedral.Cyclic
