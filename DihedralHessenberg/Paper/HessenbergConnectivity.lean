import DihedralHessenberg.Paper.HessenbergBasic
import DihedralHessenberg.Dihedral.CoxeterSystem

/-! # Connectivity through the selected Hessenberg reflection edges -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A function unchanged along all reflection edges equals its identity value everywhere. -/
theorem eq_identity_of_eq_on_reflection_edges (ideal : HessenbergSpace n hthree)
    {A : Sort*} (value : DihedralGroup n → A)
    (hedge : ∀ element index, index ∈ ideal.roots →
      value element = value (element * rootReflection index)) :
    ∀ element, value element = value 1 := by
  have hfirst : rootReflection (firstSimpleRootIndex n hthree) = firstSimpleReflection n :=
    rootReflection_first (by omega)
  have hsecond : rootReflection (secondSimpleRootIndex n hthree) = secondSimpleReflection n :=
    rootReflection_second (by omega)
  intro element
  apply (coxeterSystem n hthree).simple_induction_right (p := fun vertex => value vertex = value 1)
    element rfl
  intro previous simple ih
  rw [coxeterSystem_simple]
  fin_cases simple
  · change value (previous * simpleReflection n 0) = value 1
    rw [simpleReflection_zero]
    calc
      value (previous * firstSimpleReflection n) = value previous := by
        simpa only [hfirst] using
          (hedge previous (firstSimpleRootIndex n hthree) ideal.first_mem).symm
      _ = value 1 := ih
  · change value (previous * simpleReflection n 1) = value 1
    rw [simpleReflection_one]
    calc
      value (previous * secondSimpleReflection n) = value previous := by
        simpa only [hsecond] using
          (hedge previous (secondSimpleRootIndex n hthree) ideal.second_mem).symm
      _ = value 1 := ih

/-- The selected reflection edges force equal values at every pair of vertices. -/
theorem eq_of_eq_on_reflection_edges (ideal : HessenbergSpace n hthree)
    {A : Sort*} (value : DihedralGroup n → A)
    (hedge : ∀ element index, index ∈ ideal.roots →
      value element = value (element * rootReflection index))
    (first second : DihedralGroup n) : value first = value second :=
  (ideal.eq_identity_of_eq_on_reflection_edges value hedge first).trans
    (ideal.eq_identity_of_eq_on_reflection_edges value hedge second).symm

end Schubert.DihedralSplines.HessenbergSpace
