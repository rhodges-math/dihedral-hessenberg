import Schubert.Splines.ReflectionGraph

/-! # Dot actions on reflection splines

The dot action applies a group element to a spline value after translating its vertex
by the inverse group element. It preserves the spline conditions and defines algebra
automorphisms over the base coefficient ring.
-/

namespace Schubert.Splines.ReflectionGraphData

universe u v w z

variable {K : Type u} {S : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable (data : ReflectionGraphData K S W T)

/-- Dot translation of a vertex function with simultaneous action on its values. -/
def dotFunction (element : W) (value : W → S) : W → S :=
  fun vertex => data.action element (value (element⁻¹ * vertex))

/-- Dot translation preserves the right reflection spline conditions. -/
theorem dotFunction_isSpline (selected : Set T) (element : W) (value : data.Spline selected) :
    (data.reflectionGraph selected).IsSpline (data.dotFunction element value) := by
  intro edge
  apply Ideal.mem_span_singleton.mpr
  have hcondition := (data.reflectionGraph selected).spline_condition value
    (element⁻¹ * edge.1, edge.2)
  have hdivisible := Ideal.mem_span_singleton.mp hcondition
  have himage := map_dvd (data.action element).toAlgHom.toRingHom hdivisible
  change data.action element (data.action (element⁻¹ * edge.1) (data.label edge.2)) ∣
    data.action element ((value : W → S) (element⁻¹ * edge.1) -
      (value : W → S) ((element⁻¹ * edge.1) * data.reflection edge.2)) at himage
  simpa only [dotFunction, reflectionGraph, map_sub, ← data.action_mul_apply,
    mul_inv_cancel_left, mul_assoc] using himage

/-- The dot action of a group element on a reflection spline. -/
def dot (selected : Set T) (element : W) (value : data.Spline selected) :
    data.Spline selected :=
  ⟨data.dotFunction element value, data.dotFunction_isSpline selected element value⟩

theorem dot_apply (selected : Set T) (element : W) (value : data.Spline selected)
    (vertex : W) :
    (data.dot selected element value : W → S) vertex =
      data.action element ((value : W → S) (element⁻¹ * vertex)) :=
  rfl

/-- The identity fixes every spline under the dot action. -/
theorem dot_one (selected : Set T) (value : data.Spline selected) :
    data.dot selected 1 value = value := by
  apply Subtype.ext
  funext vertex
  simp only [dot, dotFunction, inv_one, one_mul, data.action_one_apply]

/-- A product acts by composing the corresponding dot actions. -/
theorem dot_mul (selected : Set T) (first second : W) (value : data.Spline selected) :
    data.dot selected (first * second) value =
      data.dot selected first (data.dot selected second value) := by
  apply Subtype.ext
  funext vertex
  simp only [dot, dotFunction, data.action_mul_apply, mul_inv_rev, mul_assoc]

/-- The dot action preserves sums of splines. -/
theorem dot_add (selected : Set T) (element : W) (first second : data.Spline selected) :
    data.dot selected element (first + second) =
      data.dot selected element first + data.dot selected element second := by
  apply Subtype.ext
  funext vertex
  exact map_add (data.action element) _ _

/-- The dot action preserves products of splines. -/
theorem dot_mul_splines (selected : Set T) (element : W) (first second : data.Spline selected) :
    data.dot selected element (first * second) =
      data.dot selected element first * data.dot selected element second := by
  apply Subtype.ext
  funext vertex
  exact map_mul (data.action element) _ _

/-- Dot translation is semilinear for multiplication by constant splines. -/
theorem dot_leftScalar (selected : Set T) (element : W) (scalar : S)
    (value : data.Spline selected) :
    data.dot selected element (data.leftScalar selected scalar value) =
      data.leftScalar selected (data.action element scalar) (data.dot selected element value) := by
  apply Subtype.ext
  funext vertex
  exact map_mul (data.action element) _ _

/-- Dot translation is linear for multiplication by orbit splines. -/
theorem dot_rightScalar (selected : Set T) (element : W) (scalar : S)
    (value : data.Spline selected) :
    data.dot selected element (data.rightScalar selected scalar value) =
      data.rightScalar selected scalar (data.dot selected element value) := by
  apply Subtype.ext
  funext vertex
  change data.action element
      (data.action (element⁻¹ * vertex) scalar * (value : W → S) (element⁻¹ * vertex)) =
    data.action vertex scalar * data.action element ((value : W → S) (element⁻¹ * vertex))
  rw [map_mul, ← data.action_mul_apply, mul_inv_cancel_left]

/-- Orbit splines are fixed by every dot translation. -/
theorem dot_orbitSpline (selected : Set T) (element : W) (scalar : S) :
    data.dot selected element (data.orbitSpline selected scalar) =
      data.orbitSpline selected scalar := by
  apply Subtype.ext
  funext vertex
  change data.action element (data.action (element⁻¹ * vertex) scalar) = data.action vertex scalar
  rw [← data.action_mul_apply, mul_inv_cancel_left]

/-- Dot translation as an algebra automorphism over the base coefficient ring. -/
def dotEquiv (selected : Set T) (element : W) :
    data.Spline selected ≃ₐ[K] data.Spline selected where
  toFun := data.dot selected element
  invFun := data.dot selected element⁻¹
  left_inv value := by
    rw [← data.dot_mul, inv_mul_cancel, data.dot_one]
  right_inv value := by
    rw [← data.dot_mul, mul_inv_cancel, data.dot_one]
  map_mul' := data.dot_mul_splines selected element
  map_add' := data.dot_add selected element
  commutes' scalar := by
    apply Subtype.ext
    funext vertex
    change data.action element (algebraMap K S scalar) = algebraMap K S scalar
    exact (data.action element).commutes scalar

theorem dotEquiv_apply (selected : Set T) (element : W) (value : data.Spline selected) :
    data.dotEquiv selected element value = data.dot selected element value :=
  rfl

/-- The group homomorphism giving the dot action on the spline algebra. -/
def dotAction (selected : Set T) :
    W →* (data.Spline selected ≃ₐ[K] data.Spline selected) where
  toFun := data.dotEquiv selected
  map_one' := by
    apply AlgEquiv.ext
    intro value
    exact data.dot_one selected value
  map_mul' first second := by
    apply AlgEquiv.ext
    intro value
    exact data.dot_mul selected first second value

theorem dotAction_apply (selected : Set T) (element : W) (value : data.Spline selected) :
    data.dotAction selected element value = data.dot selected element value :=
  rfl

end Schubert.Splines.ReflectionGraphData
