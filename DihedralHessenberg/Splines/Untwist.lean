import DihedralHessenberg.Splines.DotAction
import Mathlib.Algebra.Ring.Divisibility.Basic

/-! # Untwisting orbit scalar structures

Applying the inverse vertex automorphism converts the reflection spline condition
to constant reflection labels. This auxiliary graph makes the right polynomial
scalar structure an ordinary constant scalar structure for triangular elimination.
-/

namespace Schubert.Splines.ReflectionGraphData

universe u v w z

variable {K : Type u} {S : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable (data : ReflectionGraphData K S W T)

/-- An auxiliary graph with the same endpoints and vertex-independent labels. -/
def fixedLabelGraph (selected : Set T) : IdealLabeledGraph S W (W × selected) where
  source edge := edge.1
  target edge := edge.1 * data.reflection edge.2
  label edge := Ideal.span {data.label edge.2}

/-- Vertex inverse action on coefficient functions. -/
def untwistFunction (value : W → S) (vertex : W) : S :=
  data.action vertex⁻¹ (value vertex)

/-- Vertex action on coefficient functions. -/
def twistFunction (value : W → S) (vertex : W) : S :=
  data.action vertex (value vertex)

/-- Untwisting converts every reflection spline to a fixed-label spline. -/
theorem untwistFunction_isSpline (selected : Set T) (value : data.Spline selected) :
    (data.fixedLabelGraph selected).IsSpline (data.untwistFunction value) := by
  intro edge
  apply Ideal.mem_span_singleton.2
  have horiginal := Ideal.mem_span_singleton.1 (value.property edge)
  have hpulled := map_dvd (data.action edge.1⁻¹).toRingHom horiginal
  change data.action edge.1⁻¹ (data.action edge.1 (data.label edge.2)) ∣
    data.action edge.1⁻¹ ((value : W → S) edge.1 -
      (value : W → S) (edge.1 * data.reflection edge.2)) at hpulled
  have hfirst : data.label edge.2 ∣
      data.action edge.1⁻¹ ((value : W → S) edge.1) -
        data.action edge.1⁻¹ ((value : W → S) (edge.1 * data.reflection edge.2)) := by
    simpa only [map_sub, ← data.action_mul_apply, inv_mul_cancel,
      data.action_one_apply] using hpulled
  have hsecond := data.reflection_difference edge.2
    (data.action edge.1⁻¹ ((value : W → S) (edge.1 * data.reflection edge.2)))
  have hsum := dvd_add hfirst hsecond
  have hinverse : (data.reflection edge.2)⁻¹ = data.reflection edge.2 :=
    inv_eq_of_mul_eq_one_left (data.reflection_square edge.2)
  change data.label edge.2 ∣
    data.action edge.1⁻¹ ((value : W → S) edge.1) -
      data.action (edge.1 * data.reflection edge.2)⁻¹
        ((value : W → S) (edge.1 * data.reflection edge.2))
  simpa only [sub_add_sub_cancel, mul_inv_rev, hinverse, data.action_mul_apply] using hsum

/-- Twisting converts every fixed-label spline to a reflection spline. -/
theorem twistFunction_isSpline (selected : Set T)
    (value : (data.fixedLabelGraph selected).Spline) :
    (data.reflectionGraph selected).IsSpline (data.twistFunction value) := by
  intro edge
  apply Ideal.mem_span_singleton.2
  have hfirst := Ideal.mem_span_singleton.1 (value.property edge)
  change data.label edge.2 ∣ (value : W → S) edge.1 -
    (value : W → S) (edge.1 * data.reflection edge.2) at hfirst
  have hsecond := data.reflection_difference edge.2
    ((value : W → S) (edge.1 * data.reflection edge.2))
  have hsum := dvd_add hfirst hsecond
  have hmapped := map_dvd (data.action edge.1).toRingHom hsum
  change data.action edge.1 (data.label edge.2) ∣ data.action edge.1 _ at hmapped
  change data.action edge.1 (data.label edge.2) ∣
    data.action edge.1 ((value : W → S) edge.1) -
      data.action (edge.1 * data.reflection edge.2)
        ((value : W → S) (edge.1 * data.reflection edge.2))
  simpa only [sub_add_sub_cancel, map_sub, data.action_mul_apply] using hmapped

/-- Untwisting is a base-ring algebra equivalence of the two spline algebras. -/
def untwistEquiv (selected : Set T) :
    data.Spline selected ≃ₐ[K] (data.fixedLabelGraph selected).Spline where
  toFun value := ⟨data.untwistFunction value, data.untwistFunction_isSpline selected value⟩
  invFun value := ⟨data.twistFunction value, data.twistFunction_isSpline selected value⟩
  left_inv value := by
    apply Subtype.ext
    funext vertex
    change data.action vertex (data.action vertex⁻¹ ((value : W → S) vertex)) = _
    rw [← data.action_mul_apply, mul_inv_cancel, data.action_one_apply]
  right_inv value := by
    apply Subtype.ext
    funext vertex
    change data.action vertex⁻¹ (data.action vertex ((value : W → S) vertex)) = _
    rw [← data.action_mul_apply, inv_mul_cancel, data.action_one_apply]
  map_add' first second := by
    apply Subtype.ext
    funext vertex
    exact map_add (data.action vertex⁻¹) _ _
  map_mul' first second := by
    apply Subtype.ext
    funext vertex
    exact map_mul (data.action vertex⁻¹) _ _
  commutes' scalar := by
    apply Subtype.ext
    funext vertex
    exact (data.action vertex⁻¹).commutes scalar

/-- The untwisted value at a vertex is obtained by inverse coefficient action. -/
theorem untwistEquiv_apply (selected : Set T) (value : data.Spline selected) (vertex : W) :
    (data.untwistEquiv selected value : W → S) vertex =
      data.action vertex⁻¹ ((value : W → S) vertex) :=
  rfl

/-- Untwisting turns orbit scalar multiplication into ordinary scalar multiplication. -/
theorem untwistEquiv_rightScalar (selected : Set T) (scalar : S)
    (value : data.Spline selected) :
    data.untwistEquiv selected (data.rightScalar selected scalar value) =
      scalar • data.untwistEquiv selected value := by
  apply Subtype.ext
  funext vertex
  change data.action vertex⁻¹
      (data.action vertex scalar * (value : W → S) vertex) =
    scalar * data.action vertex⁻¹ ((value : W → S) vertex)
  rw [map_mul, ← data.action_mul_apply, inv_mul_cancel, data.action_one_apply]

/-- The right spline module is linearly equivalent to the ordinary fixed-label spline module. -/
def rightUntwistLinearEquiv (selected : Set T) :
    letI := data.rightAlgebra selected
    data.Spline selected ≃ₗ[S] (data.fixedLabelGraph selected).Spline := by
  letI := data.rightAlgebra selected
  exact {
    toFun := data.untwistEquiv selected
    invFun := (data.untwistEquiv selected).symm
    left_inv := (data.untwistEquiv selected).left_inv
    right_inv := (data.untwistEquiv selected).right_inv
    map_add' := (data.untwistEquiv selected).map_add
    map_smul' := fun scalar value => data.untwistEquiv_rightScalar selected scalar value }

/-- Untwisting converts the dot action to pure translation of the vertex argument. -/
theorem untwistEquiv_dot_apply (selected : Set T) (element : W)
    (value : data.Spline selected) (vertex : W) :
    (data.untwistEquiv selected (data.dot selected element value) : W → S) vertex =
      (data.untwistEquiv selected value : W → S) (element⁻¹ * vertex) := by
  change data.action vertex⁻¹
      (data.action element ((value : W → S) (element⁻¹ * vertex))) =
    data.action (element⁻¹ * vertex)⁻¹ ((value : W → S) (element⁻¹ * vertex))
  rw [← data.action_mul_apply, mul_inv_rev, inv_inv]

end Schubert.Splines.ReflectionGraphData
