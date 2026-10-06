import Schubert.Splines.ReflectionGraph

/-! # Indexed reflection edges and their endpoint pairs

Injective reflection indices make the indexed edges equivalent to their ordered
endpoint pairs. Reversing an edge negates the polynomial label and leaves its
principal ideal unchanged.
-/

namespace Schubert.Splines.ReflectionGraphData

universe u v w z

variable {K : Type u} {S : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable (data : ReflectionGraphData K S W T)

/-- Distinct reflection indices identify indexed edges with their ordered endpoint pairs. -/
noncomputable def reflectionEdgesEquiv (selected : Set T)
    (hreflection : Function.Injective data.reflection) :
    (W × selected) ≃
      {pair : W × W // ∃ index ∈ selected, pair.2 = pair.1 * data.reflection index} :=
  Equiv.ofBijective
    (fun edge => ⟨(edge.1, edge.1 * data.reflection edge.2),
      edge.2, edge.2.property, rfl⟩)
    ⟨by
      intro first second heq
      have hsource := congrArg (fun edge => edge.val.1) heq
      have htarget := congrArg (fun edge => edge.val.2) heq
      change first.1 = second.1 at hsource
      change first.1 * data.reflection first.2 = second.1 * data.reflection second.2 at htarget
      apply Prod.ext hsource
      apply Subtype.ext
      apply hreflection
      exact mul_left_cancel (by simpa only [hsource] using htarget), by
      rintro ⟨⟨source, target⟩, index, hindex, htarget⟩
      refine ⟨(source, ⟨index, hindex⟩), ?_⟩
      apply Subtype.ext
      change (source, source * data.reflection index) = (source, target)
      change target = source * data.reflection index at htarget
      rw [htarget]⟩

/-- The endpoint equivalence sends an indexed edge to its source and target. -/
theorem reflectionEdgesEquiv_apply (selected : Set T)
    (hreflection : Function.Injective data.reflection) (edge : W × selected) :
    (data.reflectionEdgesEquiv selected hreflection edge).val =
      ((data.reflectionGraph selected).source edge, (data.reflectionGraph selected).target edge) :=
  rfl

/-- Reversing a reflection edge does not change the principal ideal labeling it. -/
theorem reflectionGraph_label_reverse (selected : Set T) (vertex : W) (index : selected) :
    (data.reflectionGraph selected).label (vertex * data.reflection index, index) =
      (data.reflectionGraph selected).label (vertex, index) := by
  change Ideal.span {data.action (vertex * data.reflection index) (data.label index)} =
    Ideal.span {data.action vertex (data.label index)}
  rw [data.reflection_label_reverse, Ideal.span_singleton_neg]

end Schubert.Splines.ReflectionGraphData
