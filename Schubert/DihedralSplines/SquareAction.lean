import Schubert.Dihedral.RootReflectionAction
import Schubert.Dihedral.RankTwoRootVectors
import Schubert.Dihedral.RootAlternatingLength
import Schubert.Dihedral.ScalarCharacters
import Schubert.Dihedral.RootNumbering
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The simple reflection operators of the square -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- The first square reflection reverses the first coordinate. -/
theorem square_first_action (vector : ComplexPlane) :
    vectorOperator 4 (simpleRoot 4 (by decide) 0).reflection vector =
      ![-vector 0, vector 1] := by
  rw [simpleRoot_reflection, simpleReflection_zero]
  ext coordinate
  fin_cases coordinate <;>
    simp [vectorOperator, firstSimpleReflection, unitRootAt, complexify, complexReflection,
      complexBilinearForm, complexPairing]
  all_goals ring

/-- The second square reflection interchanges the two coordinates. -/
theorem square_second_action (vector : ComplexPlane) :
    vectorOperator 4 (simpleRoot 4 (by decide) 1).reflection vector =
      ![vector 1, vector 0] := by
  rw [simpleRoot_reflection, simpleReflection_one]
  change vectorOperator 4 (.sr (1 : ZMod 4)) vector = _
  have hop := vectorOperator_sr_natCast 4 1
  norm_num only [Nat.cast_one] at hop
  rw [hop]
  have hangle : 2 * Real.pi * (1 : ℝ) / 4 = Real.pi / 2 := by ring
  rw [hangle]
  ext coordinate
  fin_cases coordinate <;>
    simp [complexReflection, complexBilinearForm, complexPairing, complexify, unitRootAt,
      complexRotation]
  all_goals ring

/-- Both simple square reflections have sign minus one. -/
theorem square_simple_sign (simple : Fin 2) :
    signCharacter 4 (simpleRoot 4 (by decide) simple).reflection = -1 := by
  rw [simpleRoot_reflection]
  fin_cases simple
  · exact signCharacter_sr 4 0
  · exact signCharacter_sr 4 1

/-- The first simple square reflection has the diagonal matrix in the coordinate basis. -/
theorem square_first_matrix :
    LinearMap.toMatrix' (vectorRepresentation 4 (simpleRoot 4 (by decide) 0).reflection) =
      !![-1, 0; 0, 1] := by
  change LinearMap.toMatrix' (vectorOperator 4 _) = _
  ext row column
  rw [LinearMap.toMatrix'_apply, square_first_action]
  fin_cases row <;> fin_cases column <;> simp

/-- The second simple square reflection has the coordinate-interchange matrix. -/
theorem square_second_matrix :
    LinearMap.toMatrix' (vectorRepresentation 4 (simpleRoot 4 (by decide) 1).reflection) =
      !![0, 1; 1, 0] := by
  change LinearMap.toMatrix' (vectorOperator 4 _) = _
  ext row column
  rw [LinearMap.toMatrix'_apply, square_second_action]
  fin_cases row <;> fin_cases column <;> simp

/-- Both alternating four-reflection words equal the canonical longest square element. -/
theorem square_longest (first second : PositiveRoot 4)
    (hpair : (first = simpleRoot 4 (by decide) 0 ∧ second = simpleRoot 4 (by decide) 1) ∨
      (first = simpleRoot 4 (by decide) 1 ∧ second = simpleRoot 4 (by decide) 0)) :
    first.reflection * second.reflection * first.reflection * second.reflection =
      longestElement 4 (by decide) := by
  have hlength := PositiveRoot.alternating_length first second hpair 4 (by decide)
  rw [length_eq_longest] at hlength
  convert hlength using 1
  change first.reflection * second.reflection * first.reflection * second.reflection =
    first.alternatingProduct second (2 * 2)
  rw [PositiveRoot.alternating_even, pow_two]
  group

/-- The third positive square root has the first-second-first reflection word. -/
theorem square_third_reflection :
    (positiveRootEquiv 4 ⟨2, by decide⟩).reflection =
      (simpleRoot 4 (by decide) 0).reflection * (simpleRoot 4 (by decide) 1).reflection *
        (simpleRoot 4 (by decide) 0).reflection := by
  have hword := numbered_even_reflection 4 1 (by decide)
  simpa only [pow_one, simpleRoot_reflection, simpleReflection_zero, simpleReflection_one]
    using hword

/-- The third square-root reflection also has sign minus one. -/
theorem square_third_sign :
    signCharacter 4 (positiveRootEquiv 4 ⟨2, by decide⟩).reflection = -1 := by
  rw [square_third_reflection]
  simp only [map_mul, square_simple_sign]
  norm_num

/-- The trivial scalar representation takes the value one at both square generators. -/
theorem square_simple_trivial (simple : Fin 2) :
    Representation.trivial ℂ (DihedralGroup 4) ℂ
      (simpleRoot 4 (by decide) simple).reflection 1 = 1 := rfl

/-- The trivial square representation has character one at every group element. -/
theorem square_trivial_character (element : DihedralGroup 4) :
    (Representation.trivial ℂ (DihedralGroup 4) ℂ).character element = 1 := by
  change LinearMap.trace ℂ ℂ LinearMap.id = 1
  simp

end Schubert.DihedralSplines
