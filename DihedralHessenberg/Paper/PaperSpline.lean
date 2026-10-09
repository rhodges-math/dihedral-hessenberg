import DihedralHessenberg.Paper.PaperGraph
import DihedralHessenberg.Splines.SplineDegree

/-! # The geometric spline function algebra -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n)

/-- The geometric reflection spline condition for a vector subset. -/
def IsSpline (value : DihedralGroup n → CoordinatePolynomial) : Prop :=
  ∀ vertex alpha (hmem : alpha ∈ selected),
    linearPolynomial (complexify (realAction n vertex alpha)) ∣
      value vertex - value (vertex * (selected.root alpha hmem).reflection)

/-- The geometric condition equals the polynomial-labelled endpoint condition. -/
theorem isSpline_iff_graph (value : DihedralGroup n → CoordinatePolynomial) :
    selected.IsSpline value ↔ selected.graph.IsSpline value := by
  constructor
  · intro hvalue pair
    have hcondition := hvalue pair.val.1 (selected.edgeRoot pair).val
      (selected.edgeRoot_mem pair)
    have hroot : selected.root (selected.edgeRoot pair).val
        (selected.edgeRoot_mem pair) = selected.edgeRoot pair := Subtype.ext rfl
    rw [hroot] at hcondition
    change selected.edgeLabel pair ∣ value pair.val.1 - value pair.val.2
    rw [selected.edgeRoot_endpoint pair]
    exact hcondition
  · intro hvalue vertex alpha hmem
    have hrootmem : (selected.root alpha hmem).val ∈ selected := hmem
    have hedge := hvalue (selected.edge vertex (selected.root alpha hmem) hrootmem)
    change selected.edgeLabel (selected.edge vertex (selected.root alpha hmem) hrootmem) ∣
      value vertex - value (vertex * (selected.root alpha hmem).reflection) at hedge
    rw [edgeLabel_edge] at hedge
    exact hedge

/-- Geometric splines form a complex subalgebra with pointwise operations. -/
def splineAlgebra : Subalgebra ℂ (DihedralGroup n → CoordinatePolynomial) where
  carrier := {value | selected.IsSpline value}
  algebraMap_mem' scalar := by
    intro vertex alpha hmem
    change _ ∣ MvPolynomial.C scalar - MvPolynomial.C scalar
    rw [sub_self]
    exact dvd_zero _
  add_mem' first second := (selected.isSpline_iff_graph _).2
    ((selected.graph.isSpline_iff _).2 (selected.graph.idealGraph.isSpline_add
      ((selected.graph.isSpline_iff _).1 ((selected.isSpline_iff_graph _).1 first))
      ((selected.graph.isSpline_iff _).1 ((selected.isSpline_iff_graph _).1 second))))
  mul_mem' first second := (selected.isSpline_iff_graph _).2
    ((selected.graph.isSpline_iff _).2 (selected.graph.idealGraph.isSpline_mul
      ((selected.graph.isSpline_iff _).1 ((selected.isSpline_iff_graph _).1 first))
      ((selected.graph.isSpline_iff _).1 ((selected.isSpline_iff_graph _).1 second))))

/-- The polynomial-valued geometric spline algebra. -/
abbrev Spline := ↥selected.splineAlgebra

/-- Membership is precisely the displayed geometric divisibility condition. -/
theorem mem_splineAlgebra (value : DihedralGroup n → CoordinatePolynomial) :
    value ∈ selected.splineAlgebra ↔ selected.IsSpline value := Iff.rfl

/-- Geometric and indexed spline conditions coincide without changing vertex values. -/
theorem isSpline_iff_backend (hthree : 3 ≤ n)
    (value : DihedralGroup n → CoordinatePolynomial) :
    selected.IsSpline value ↔
      ((dihedralReflectionData n hthree).reflectionGraph selected.indices).IsSpline value := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  rw [dihedralReflectionGraph_isSpline_iff]
  constructor
  · intro hvalue vertex index hindex
    have hroot : selected.root (positiveRoot n index) hindex = positiveRootEquiv n index :=
      Subtype.ext rfl
    have hcondition := hvalue vertex (positiveRoot n index) hindex
    rw [hroot, PositiveRoot.reflection_equiv,
      realAction_complexify n vertex _ (Or.inl ⟨index, rfl⟩)] at hcondition
    exact hcondition
  · intro hvalue vertex alpha hmem
    obtain ⟨index, rfl⟩ := selected.positive hmem
    have hroot : selected.root (positiveRoot n index) hmem = positiveRootEquiv n index :=
      Subtype.ext rfl
    rw [hroot, PositiveRoot.reflection_equiv,
      realAction_complexify n vertex _ (Or.inl ⟨index, rfl⟩)]
    exact hvalue vertex index hmem

/-- The geometric-to-indexed bridge is an evaluation-preserving complex algebra equivalence. -/
def backendEquiv (hthree : 3 ≤ n) : selected.Spline ≃ₐ[ℂ]
    (dihedralReflectionData n hthree).Spline selected.indices where
  toFun value := ⟨value.val, (selected.isSpline_iff_backend hthree value.val).1 value.property⟩
  invFun value := ⟨value.val, (selected.isSpline_iff_backend hthree value.val).2 value.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The algebra equivalence preserves each function evaluation. -/
theorem backendEquiv_apply (hthree : 3 ≤ n) (value : selected.Spline)
    (vertex : DihedralGroup n) :
    (selected.backendEquiv hthree value : DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) vertex := rfl

/-- The whole-spline degree is the maximum total degree of its vertex values. -/
def degree [NeZero n] (value : selected.Spline) : ℕ :=
  Finset.univ.sup fun vertex =>
    ((value : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree

/-- A degree bound for the entire spline is equivalent to a bound at every vertex. -/
theorem degree_le_iff [NeZero n] (value : selected.Spline) (bound : ℕ) :
    selected.degree value ≤ bound ↔
      ∀ vertex, ((value : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤ bound := by
  classical
  simp only [degree, Finset.sup_le_iff, Finset.mem_univ, forall_const]

/-- The evaluation-preserving bridge preserves the whole-spline degree. -/
theorem backendEquiv_degree [NeZero n] (hthree : 3 ≤ n) (value : selected.Spline) :
    ((dihedralReflectionData n hthree).reflectionGraph selected.indices).degreeBound
      (selected.backendEquiv hthree value) = selected.degree value := rfl

end Schubert.Dihedral.RootSubset
