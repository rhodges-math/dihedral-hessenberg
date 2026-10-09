import DihedralHessenberg.Splines.DotAction
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Dividing a dot difference by a reflection label

The polynomial quotient is determined by its multiplied numerator equation.
Relatively prime edge labels allow cancellation; parallel reflection edges use
reflection equivariance of the quotient instead.
-/

namespace Schubert.Splines.ReflectionGraphData

variable {K S W T : Type*} [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable [IsDomain S] (data : ReflectionGraphData K S W T) (selected : Set T)
variable (index : T) (value : data.Spline selected) (quotient : W → S)
variable (hlabel : data.label index ≠ 0)
variable (hquotient : ∀ vertex, data.label index * quotient vertex =
  (value : W → S) vertex -
    (data.dot selected (data.reflection index) value : W → S) vertex)

include hlabel hquotient in
/-- A polynomial quotient of a reflection dot difference is reflection-equivariant. -/
theorem reflection_dot_quotient_equivariant (vertex : W) :
    quotient (data.reflection index * vertex) =
      data.action (data.reflection index) (quotient vertex) := by
  have hinverse : (data.reflection index)⁻¹ = data.reflection index :=
    inv_eq_of_mul_eq_one_left (data.reflection_square index)
  have hfirst := hquotient vertex
  have hsecond := hquotient (data.reflection index * vertex)
  have himage := congrArg (data.action (data.reflection index)) hfirst
  simp only [dot_apply, hinverse, ← mul_assoc, data.reflection_square, one_mul]
    at hfirst hsecond himage
  rw [map_mul, data.reflection_label, map_sub, ← data.action_mul_apply,
    data.reflection_square, data.action_one_apply] at himage
  apply mul_left_cancel₀ hlabel
  calc
    data.label index * quotient (data.reflection index * vertex) =
        (value : W → S) (data.reflection index * vertex) -
          data.action (data.reflection index) ((value : W → S) vertex) := hsecond
    _ = data.label index * data.action (data.reflection index) (quotient vertex) := by
      linear_combination himage

omit [IsDomain S] in
/-- Polynomial divisibility of a dot numerator follows from the reflection-pair difference. -/
theorem label_dvd_dot_numerator (vertex : W)
    (hpair : data.label index ∣ (value : W → S) vertex -
      (value : W → S) (data.reflection index * vertex)) :
    data.label index ∣ (value : W → S) vertex -
      (data.dot selected (data.reflection index) value : W → S) vertex := by
  have hinverse : (data.reflection index)⁻¹ = data.reflection index :=
    inv_eq_of_mul_eq_one_left (data.reflection_square index)
  rw [dot_apply, hinverse]
  have hreflected := data.reflection_difference index
    ((value : W → S) (data.reflection index * vertex))
  convert dvd_add hpair hreflected using 1
  ring

include hlabel hquotient in
/-- A divided dot difference is a spline when each edge is transverse or the reflection pair. -/
theorem reflection_dot_quotient_isSpline [DecompositionMonoid S]
    (hedges : ∀ vertex edgeIndex, edgeIndex ∈ selected →
      IsRelPrime (data.action vertex (data.label edgeIndex)) (data.label index) ∨
        (Associated (data.action vertex (data.label edgeIndex)) (data.label index) ∧
          vertex * data.reflection edgeIndex = data.reflection index * vertex)) :
    (data.reflectionGraph selected).IsSpline quotient := by
  intro edge
  apply Ideal.mem_span_singleton.mpr
  have hdivides := Ideal.mem_span_singleton.mp
    ((data.reflectionGraph selected).spline_condition
      (value - data.dot selected (data.reflection index) value) edge)
  change data.action edge.1 (data.label edge.2) ∣
    ((value : W → S) edge.1 -
      (data.dot selected (data.reflection index) value : W → S) edge.1) -
    ((value : W → S) (edge.1 * data.reflection edge.2) -
      (data.dot selected (data.reflection index) value : W → S)
        (edge.1 * data.reflection edge.2)) at hdivides
  have hmultiple : data.label index *
      (quotient edge.1 - quotient (edge.1 * data.reflection edge.2)) =
        ((value : W → S) edge.1 -
          (data.dot selected (data.reflection index) value : W → S) edge.1) -
        ((value : W → S) (edge.1 * data.reflection edge.2) -
          (data.dot selected (data.reflection index) value : W → S)
            (edge.1 * data.reflection edge.2)) := by
    rw [mul_sub, hquotient, hquotient]
  rcases hedges edge.1 edge.2 edge.2.property with hprime | ⟨hassociated, htarget⟩
  · rw [← hmultiple] at hdivides
    exact hprime.dvd_of_dvd_mul_left hdivides
  · change data.action edge.1 (data.label edge.2) ∣
      quotient edge.1 - quotient (edge.1 * data.reflection edge.2)
    rw [htarget, data.reflection_dot_quotient_equivariant
      selected index value quotient hlabel hquotient]
    exact hassociated.dvd.trans (data.reflection_difference index (quotient edge.1))

end Schubert.Splines.ReflectionGraphData
