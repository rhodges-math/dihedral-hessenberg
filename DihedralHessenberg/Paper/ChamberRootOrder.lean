import DihedralHessenberg.Dihedral.RootFrame
import DihedralHessenberg.Paper.RootOrder

/-! # Transport of the real simple-root cone through root chambers -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Every chamber frame carries the nonnegative simple-root cone order. -/
theorem chamber_order {n : ℕ} [NeZero n] {data : Separator n}
    (frame : data.Frame) (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) :
    (∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
      (frame.root beta).val - (frame.root alpha).val =
        first • (frame.first hthree).val + second • (frame.second hthree).val) ↔
      RootOrder n hthree alpha beta := by
  let action := realLinearEquiv n frame.element
  change (∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
      action beta.val - action alpha.val =
        first • action (simpleRoot n hthree 0).val +
          second • action (simpleRoot n hthree 1).val) ↔ _
  constructor
  · rintro ⟨first, second, hfirst, hsecond, heq⟩
    refine ⟨first, second, hfirst, hsecond, action.injective ?_⟩
    simpa only [map_sub, map_add, map_smul] using heq
  · rintro ⟨first, second, hfirst, hsecond, heq⟩
    refine ⟨first, second, hfirst, hsecond, ?_⟩
    simpa only [map_sub, map_add, map_smul] using congrArg action heq

end Schubert.DihedralSplines
