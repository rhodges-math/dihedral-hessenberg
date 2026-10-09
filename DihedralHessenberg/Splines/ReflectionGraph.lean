import DihedralHessenberg.Splines.Graph
import Mathlib.RingTheory.Ideal.Span

/-! # Splines on reflection graphs

A group acts on a commutative algebra, and each indexed reflection has a label whose
principal ideal contains every difference between an element and its reflected image.
An arbitrary subset of reflection indices determines right reflection edges. Constant and
orbit functions give two scalar algebra structures on the resulting spline algebra.
-/

namespace Schubert.Splines

universe u v w z

/-- Algebra automorphisms, indexed reflections, and their divisibility labels. -/
structure ReflectionGraphData (K : Type u) (S : Type v) (W : Type w) (T : Type z)
    [CommRing K] [CommRing S] [Algebra K S] [Group W] where
  /-- The action on the coefficient algebra. -/
  action : W →* (S ≃ₐ[K] S)
  /-- The reflection associated to each index. -/
  reflection : T → W
  /-- The algebra element labeling each reflection. -/
  label : T → S
  /-- Each indexed reflection is an involution. -/
  reflection_square : ∀ index, reflection index * reflection index = 1
  /-- A reflection negates its own label. -/
  reflection_label : ∀ index, action (reflection index) (label index) = -label index
  /-- Reflection differences are divisible by the corresponding label. -/
  reflection_difference : ∀ index value, label index ∣ value - action (reflection index) value

namespace ReflectionGraphData

variable {K : Type u} {S : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable (data : ReflectionGraphData K S W T)

/-- The right reflection graph on a selected subset of reflection indices. -/
def reflectionGraph (selected : Set T) : IdealLabeledGraph S W (W × selected) where
  source edge := edge.1
  target edge := edge.1 * data.reflection edge.2
  label edge := Ideal.span {data.action edge.1 (data.label edge.2)}

/-- The spline algebra on the selected right reflection graph. -/
abbrev Spline (selected : Set T) := (data.reflectionGraph selected).Spline

/-- Multiplication of group elements acts by composition on algebra elements. -/
theorem action_mul_apply (first second : W) (value : S) :
    data.action (first * second) value = data.action first (data.action second value) := by
  rw [data.action.map_mul]
  rfl

/-- The identity group element acts trivially on the coefficient algebra. -/
theorem action_one_apply (value : S) : data.action 1 value = value := by
  rw [data.action.map_one]
  rfl

/-- Traversing a reflection edge twice returns to its initial vertex. -/
theorem reflection_edge_reverse (vertex : W) (index : T) :
    (vertex * data.reflection index) * data.reflection index = vertex := by
  rw [mul_assoc, data.reflection_square, mul_one]

/-- Reversing a reflection edge negates its generating label. -/
theorem reflection_label_reverse (vertex : W) (index : T) :
    data.action (vertex * data.reflection index) (data.label index) =
      -data.action vertex (data.label index) := by
  rw [data.action_mul_apply, data.reflection_label, map_neg]

/-- A constant function belongs to every selected reflection spline algebra. -/
def constantSpline (selected : Set T) (value : S) : data.Spline selected :=
  (data.reflectionGraph selected).constant value

theorem constantSpline_apply (selected : Set T) (value : S) (vertex : W) :
    (data.constantSpline selected value : W → S) vertex = value :=
  rfl

/-- Orbit functions satisfy the reflection-edge divisibility conditions. -/
theorem orbit_isSpline (selected : Set T) (value : S) :
    (data.reflectionGraph selected).IsSpline (fun vertex => data.action vertex value) := by
  intro edge
  apply Ideal.mem_span_singleton.mpr
  change data.action edge.1 (data.label edge.2) ∣
    data.action edge.1 value - data.action (edge.1 * data.reflection edge.2) value
  rw [data.action_mul_apply, ← map_sub]
  exact map_dvd (data.action edge.1).toAlgHom.toRingHom
    (data.reflection_difference edge.2 value)

/-- The spline obtained by applying each vertex to a fixed algebra element. -/
def orbitSpline (selected : Set T) (value : S) : data.Spline selected :=
  ⟨fun vertex => data.action vertex value, data.orbit_isSpline selected value⟩

theorem orbitSpline_apply (selected : Set T) (value : S) (vertex : W) :
    (data.orbitSpline selected value : W → S) vertex = data.action vertex value :=
  rfl

/-- Constant splines as a homomorphism from the coefficient algebra. -/
def constantHom (selected : Set T) : S →ₐ[K] data.Spline selected where
  toFun := data.constantSpline selected
  map_zero' := by apply Subtype.ext; rfl
  map_one' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl
  commutes' _ := by apply Subtype.ext; rfl

/-- Orbit splines as a homomorphism from the coefficient algebra. -/
def orbitHom (selected : Set T) : S →ₐ[K] data.Spline selected where
  toFun := data.orbitSpline selected
  map_zero' := by
    apply Subtype.ext
    funext vertex
    exact map_zero (data.action vertex)
  map_one' := by
    apply Subtype.ext
    funext vertex
    exact map_one (data.action vertex)
  map_add' first second := by
    apply Subtype.ext
    funext vertex
    exact map_add (data.action vertex) first second
  map_mul' first second := by
    apply Subtype.ext
    funext vertex
    exact map_mul (data.action vertex) first second
  commutes' scalar := by
    apply Subtype.ext
    funext vertex
    exact (data.action vertex).commutes scalar

/-- The scalar algebra structure given by constant splines. -/
@[instance_reducible]
def leftAlgebra (selected : Set T) : Algebra S (data.Spline selected) :=
  inferInstance

/-- The scalar algebra structure given by orbit splines. -/
@[instance_reducible]
def rightAlgebra (selected : Set T) : Algebra S (data.Spline selected) :=
  (data.orbitHom selected).toRingHom.toAlgebra

/-- Multiplication by a scalar through its constant spline. -/
def leftScalar (selected : Set T) (scalar : S) (value : data.Spline selected) :
    data.Spline selected :=
  data.constantSpline selected scalar * value

/-- Multiplication by a scalar through its orbit spline. -/
def rightScalar (selected : Set T) (scalar : S) (value : data.Spline selected) :
    data.Spline selected :=
  data.orbitSpline selected scalar * value

theorem leftScalar_apply (selected : Set T) (scalar : S) (value : data.Spline selected)
    (vertex : W) :
    (data.leftScalar selected scalar value : W → S) vertex = scalar * (value : W → S) vertex :=
  rfl

theorem rightScalar_apply (selected : Set T) (scalar : S) (value : data.Spline selected)
    (vertex : W) :
    (data.rightScalar selected scalar value : W → S) vertex =
      data.action vertex scalar * (value : W → S) vertex :=
  rfl

/-- The constant scalar formula is the action of the left scalar algebra structure. -/
theorem leftAlgebra_smul (selected : Set T) (scalar : S) (value : data.Spline selected) :
    letI := data.leftAlgebra selected
    scalar • value = data.leftScalar selected scalar value :=
  rfl

/-- The orbit scalar formula is the action of the right scalar algebra structure. -/
theorem rightAlgebra_smul (selected : Set T) (scalar : S) (value : data.Spline selected) :
    letI := data.rightAlgebra selected
    scalar • value = data.rightScalar selected scalar value :=
  rfl

end ReflectionGraphData

end Schubert.Splines
