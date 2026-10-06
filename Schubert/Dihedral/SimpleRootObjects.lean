import Schubert.Dihedral.RootObjects

/-! # The two simple root vectors -/

namespace Schubert.Dihedral

/-- The simple positive root with the specified generator. -/
noncomputable def simpleRoot (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2) : PositiveRoot n :=
  positiveRootEquiv n
    (if simple = 0 then firstSimpleRootIndex n hthree else secondSimpleRootIndex n hthree)

/-- The first simple vector has the first alternating index. -/
theorem simpleRoot_zero (n : ℕ) (hthree : 3 ≤ n) :
    simpleRoot n hthree 0 = positiveRootEquiv n (firstSimpleRootIndex n hthree) := by
  unfold simpleRoot
  rw [ite_eq_left rfl]

/-- The second simple vector has the second alternating index. -/
theorem simpleRoot_one (n : ℕ) (hthree : 3 ≤ n) :
    simpleRoot n hthree 1 = positiveRootEquiv n (secondSimpleRootIndex n hthree) := by
  unfold simpleRoot
  rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]

/-- The two simple vectors recover the two distinguished group generators. -/
theorem simpleRoot_reflection (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2) :
    (simpleRoot n hthree simple).reflection = simpleReflection n simple := by
  fin_cases simple
  · change (simpleRoot n hthree 0).reflection = simpleReflection n 0
    rw [simpleRoot_zero, PositiveRoot.reflection_equiv, firstSimpleRootIndex, rootReflection_first,
      simpleReflection_zero]
  · change (simpleRoot n hthree 1).reflection = simpleReflection n 1
    rw [simpleRoot_one, PositiveRoot.reflection_equiv, secondSimpleRootIndex, rootReflection_second,
      simpleReflection_one]

end Schubert.Dihedral
