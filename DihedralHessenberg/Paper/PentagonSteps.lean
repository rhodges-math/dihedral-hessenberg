import DihedralHessenberg.Paper.PentagonTop
import DihedralHessenberg.Paper.FlowupSteps

/-! # Recursion for the pentagon generators -/

noncomputable section
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral

private structure Ascent (lower upper : Fin 10) where
  simple : Fin 2
  endpoint : (simpleRoot 5 (by decide) simple).reflection * vertices lower = vertices upper
  growth : length 5 (by decide) (vertices upper) = length 5 (by decide) (vertices lower) + 1

private theorem simple_mem (simple : Fin 2) :
    simpleRoot 5 (by decide) simple = simpleRoot 5 (by decide) 0 ∨
      simpleRoot 5 (by decide) simple = simpleRoot 5 (by decide) 1 := by
  fin_cases simple <;> simp

private def tailAt {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper)) :
    HomogeneousAt ideal ((simpleRoot 5 (by decide) step.simple).reflection * vertices lower) :=
  step.endpoint.symm ▸ tail

private theorem tail_value {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper)) : (tailAt step tail).value = tail.value := by
  unfold tailAt
  have hcast {first second : DihedralGroup 5} (h : first = second)
      (value : HomogeneousAt ideal first) : (h ▸ value).value = value.value := by
    cases h
    rfl
  exact hcast _ _

private def dotAt {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper))
    (hdegree : ideal.toRootSubset.length (vertices upper) =
      ideal.toRootSubset.length (vertices lower)) : HomogeneousAt ideal (vertices lower) :=
  HomogeneousAt.dotStep (simpleRoot 5 (by decide) step.simple) (simple_mem _)
    (by rw [step.endpoint]; exact step.growth) (tailAt step tail)
    (by rw [step.endpoint]; exact hdegree)

private theorem dotAt_value {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper)) (hdegree) :
    (dotAt step tail hdegree).value =
      ideal.toRootSubset.dot (by decide) (simpleRoot 5 (by decide) step.simple).reflection
        tail.value := by
  change ideal.toRootSubset.dot (by decide)
    (simpleRoot 5 (by decide) step.simple).reflection (tailAt step tail).value = _
  rw [tail_value]

private theorem admissibleAt {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper))
    (hhalf : 5 < 2 * length 5 (by decide) (vertices lower) + 1)
    (hedge : (vertices lower, vertices upper) ∈ ideal.toRootSubset.edges) :
    ∀ vertex,
      ((tailAt step tail).value : DihedralGroup 5 → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, (simpleRoot 5 (by decide) step.simple).reflection * vertex) ∈
        ideal.toRootSubset.edges := by
  intro vertex hnonzero
  apply ideal.edge_above (simpleRoot 5 (by decide) step.simple) (simple_mem _)
    (vertices lower) (by rw [step.endpoint]; exact step.growth) hhalf
    (by rw [step.endpoint]; exact hedge) vertex
  by_contra hnot
  exact hnonzero ((tailAt step tail).support vertex hnot)

private def differenceAt {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper))
    (hdegree : ideal.toRootSubset.length (vertices upper) =
      ideal.toRootSubset.length (vertices lower) + 1)
    (hhalf : 5 < 2 * length 5 (by decide) (vertices lower) + 1)
    (hedge : (vertices lower, vertices upper) ∈ ideal.toRootSubset.edges) :
    HomogeneousAt ideal (vertices lower) :=
  HomogeneousAt.differenceStep (simpleRoot 5 (by decide) step.simple) (simple_mem _)
    (by rw [step.endpoint]; exact step.growth) (tailAt step tail)
    (admissibleAt step tail hhalf hedge)
    (by rw [step.endpoint]; exact hdegree)

private theorem differenceAt_mul {lower upper : Fin 10} (step : Ascent lower upper)
    (tail : HomogeneousAt ideal (vertices upper)) (hdegree) (hhalf) (hedge)
    (vertex : DihedralGroup 5) :
    (simpleRoot 5 (by decide) step.simple).form *
        ((differenceAt step tail hdegree hhalf hedge).value :
          DihedralGroup 5 → CoordinatePolynomial) vertex =
      (tail.value : DihedralGroup 5 → CoordinatePolynomial) vertex -
        (ideal.toRootSubset.dot (by decide)
          (simpleRoot 5 (by decide) step.simple).reflection tail.value :
            DihedralGroup 5 → CoordinatePolynomial) vertex := by
  change (simpleRoot 5 (by decide) step.simple).form *
    (ideal.dividedDifference (tailAt step tail).value
      (simpleRoot 5 (by decide) step.simple) (admissibleAt step tail hhalf hedge) :
        DihedralGroup 5 → CoordinatePolynomial) vertex = _
  rw [ideal.dividedDifference_mul, tail_value]

private def firstStep : Ascent 8 9 where
  simple := 0
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  growth := by rw [word_lengths, word_lengths]; decide

private def secondStep : Ascent 7 9 where
  simple := 1
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
    all_goals decide
  growth := by rw [word_lengths, word_lengths]; decide

private def bothStep : Ascent 5 7 where
  simple := 0
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  growth := by rw [word_lengths, word_lengths]; decide

private def leftMiddleStep : Ascent 6 8 where
  simple := 1
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  growth := by rw [word_lengths, word_lengths]; decide

private def rightMiddleStep : Ascent 4 6 where
  simple := 0
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  growth := by rw [word_lengths, word_lengths]; decide

private def leftLowStep : Ascent 3 5 where
  simple := 1
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  growth := by rw [word_lengths, word_lengths]; decide

private def rightLowStep : Ascent 1 3 where
  simple := 0
  endpoint := by
    norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  growth := by rw [word_lengths, word_lengths]; decide

/-- The homogeneous upper certificate after the indicated divided difference. -/
def afterFirst : HomogeneousAt ideal (vertices 8) :=
  differenceAt firstStep top (by rw [degrees, degrees]; decide)
    (by rw [word_lengths]; decide) (edge_mem 4)

/-- The homogeneous upper certificate after the indicated divided difference. -/
def afterSecond : HomogeneousAt ideal (vertices 7) :=
  differenceAt secondStep top (by rw [degrees, degrees]; decide)
    (by rw [word_lengths]; decide) (edge_mem 5)

/-- The homogeneous upper certificate after the indicated divided difference. -/
def afterBoth : HomogeneousAt ideal (vertices 5) :=
  differenceAt bothStep afterSecond (by rw [degrees, degrees]; decide)
    (by rw [word_lengths]; decide) (edge_mem 14)

/-- The homogeneous upper certificate after the indicated dot translation. -/
def leftMiddle : HomogeneousAt ideal (vertices 6) :=
  dotAt leftMiddleStep afterFirst (by rw [degrees, degrees]; decide)

/-- The homogeneous upper certificate after the indicated dot translation. -/
def rightMiddle : HomogeneousAt ideal (vertices 4) :=
  dotAt rightMiddleStep leftMiddle (by rw [degrees, degrees]; decide)

/-- The homogeneous upper certificate after the indicated dot translation. -/
def leftLow : HomogeneousAt ideal (vertices 3) :=
  dotAt leftLowStep afterBoth (by rw [degrees, degrees]; decide)

/-- The homogeneous upper certificate after the indicated dot translation. -/
def rightLow : HomogeneousAt ideal (vertices 1) :=
  dotAt rightLowStep leftLow (by rw [degrees, degrees]; decide)

/-- All nonzero vertices have the selected edge needed for this divided difference. -/
theorem afterFirst_admissible (vertex : DihedralGroup 5)
    (hnonzero : (top.value : DihedralGroup 5 → CoordinatePolynomial) vertex ≠ 0) :
    (vertex, (simpleRoot 5 (by decide) 0).reflection * vertex) ∈ selected.edges := by
  exact admissibleAt firstStep top (by rw [word_lengths]; decide) (edge_mem 4)
    vertex (by rwa [tail_value])

/-- This generator is the indicated divided difference. -/
theorem afterFirst_value : afterFirst.value =
    ideal.dividedDifference top.value (simpleRoot 5 (by decide) 0)
      afterFirst_admissible := by
  apply ideal.dividedDifference_unique top.value (simpleRoot 5 (by decide) 0)
    afterFirst_admissible afterFirst.value
  intro vertex
  exact differenceAt_mul firstStep top _ _ _ vertex

/-- All nonzero vertices have the selected edge needed for this divided difference. -/
theorem afterSecond_admissible (vertex : DihedralGroup 5)
    (hnonzero : (top.value : DihedralGroup 5 → CoordinatePolynomial) vertex ≠ 0) :
    (vertex, (simpleRoot 5 (by decide) 1).reflection * vertex) ∈ selected.edges := by
  exact admissibleAt secondStep top (by rw [word_lengths]; decide) (edge_mem 5)
    vertex (by rwa [tail_value])

/-- This generator is the indicated divided difference. -/
theorem afterSecond_value : afterSecond.value =
    ideal.dividedDifference top.value (simpleRoot 5 (by decide) 1)
      afterSecond_admissible := by
  apply ideal.dividedDifference_unique top.value (simpleRoot 5 (by decide) 1)
    afterSecond_admissible afterSecond.value
  intro vertex
  exact differenceAt_mul secondStep top _ _ _ vertex

/-- All nonzero vertices have the selected edge needed for this divided difference. -/
theorem afterBoth_admissible (vertex : DihedralGroup 5)
    (hnonzero : (afterSecond.value : DihedralGroup 5 → CoordinatePolynomial) vertex ≠ 0) :
    (vertex, (simpleRoot 5 (by decide) 0).reflection * vertex) ∈ selected.edges := by
  exact admissibleAt bothStep afterSecond (by rw [word_lengths]; decide) (edge_mem 14)
    vertex (by rwa [tail_value])

/-- This generator is the indicated divided difference. -/
theorem afterBoth_value : afterBoth.value =
    ideal.dividedDifference afterSecond.value (simpleRoot 5 (by decide) 0)
      afterBoth_admissible := by
  apply ideal.dividedDifference_unique afterSecond.value (simpleRoot 5 (by decide) 0)
    afterBoth_admissible afterBoth.value
  intro vertex
  exact differenceAt_mul bothStep afterSecond _ _ _ vertex

/-- This generator is its one-step dot translate. -/
theorem leftMiddle_value : leftMiddle.value =
    ideal.toRootSubset.dot (by decide) (simpleRoot 5 (by decide) 1).reflection
      afterFirst.value :=
  dotAt_value leftMiddleStep afterFirst _

/-- This generator is its one-step dot translate. -/
theorem rightMiddle_value : rightMiddle.value =
    ideal.toRootSubset.dot (by decide) (simpleRoot 5 (by decide) 0).reflection
      leftMiddle.value :=
  dotAt_value rightMiddleStep leftMiddle _

/-- This generator is its one-step dot translate. -/
theorem leftLow_value : leftLow.value =
    ideal.toRootSubset.dot (by decide) (simpleRoot 5 (by decide) 1).reflection
      afterBoth.value :=
  dotAt_value leftLowStep afterBoth _

/-- This generator is its one-step dot translate. -/
theorem rightLow_value : rightLow.value =
    ideal.toRootSubset.dot (by decide) (simpleRoot 5 (by decide) 0).reflection
      leftLow.value :=
  dotAt_value rightLowStep leftLow _

/-- The two dot steps combine to the displayed simple-reflection product. -/
theorem rightMiddle_word : rightMiddle.value =
    ideal.toRootSubset.dot (by decide)
      ((simpleRoot 5 (by decide) 0).reflection * (simpleRoot 5 (by decide) 1).reflection)
      afterFirst.value := by
  rw [rightMiddle_value, leftMiddle_value, ← RootSubset.dot_mul]

/-- The two dot steps combine to the displayed simple-reflection product. -/
theorem rightLow_word : rightLow.value =
    ideal.toRootSubset.dot (by decide)
      ((simpleRoot 5 (by decide) 0).reflection * (simpleRoot 5 (by decide) 1).reflection)
      afterBoth.value := by
  rw [rightLow_value, leftLow_value, ← RootSubset.dot_mul]

end Schubert.DihedralSplines.Pentagon
