import Schubert.Dihedral.ReflectionIndex
import Schubert.DihedralSplines.Spline
import Schubert.Splines.ReflectionEdges

/-! # The endpoint-pair model of a Hessenberg graph

The indexed edges of a Hessenberg graph are equivalent to the set of ordered
reflection endpoint pairs. Their geometric linear labels generate the existing
edge ideals; reversal changes only the sign of the chosen generator.
-/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

/-- Hessenberg indexed edges and the corresponding ordered endpoint pairs. -/
def hessenbergEdgesEquiv {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree) :
    (DihedralGroup n × {index : PositiveRootIndex n // index ∈ ideal.roots}) ≃
      {pair : DihedralGroup n × DihedralGroup n //
        ∃ index ∈ ideal.roots, pair.2 = pair.1 * rootReflection index} :=
  (dihedralReflectionData n hthree).reflectionEdgesEquiv
    (ideal.roots : Set (PositiveRootIndex n)) (rootReflection_injective n)

/-- The Hessenberg endpoint equivalence preserves each source and target. -/
theorem hessenbergEdgesEquiv_apply {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) (vertex : DihedralGroup n)
    (index : PositiveRootIndex n) (hindex : index ∈ ideal.roots) :
    (hessenbergEdgesEquiv ideal (vertex, ⟨index, hindex⟩)).val =
      (vertex, vertex * rootReflection index) :=
  rfl

/-- A reversed Hessenberg edge has the same label ideal. -/
theorem hessenbergGraph_label_reverse {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) (vertex : DihedralGroup n)
    (index : PositiveRootIndex n) (hindex : index ∈ ideal.roots) :
    (hessenbergGraph ideal).label (vertex * rootReflection index, ⟨index, hindex⟩) =
      (hessenbergGraph ideal).label (vertex, ⟨index, hindex⟩) :=
  (dihedralReflectionData n hthree).reflectionGraph_label_reverse
    (ideal.roots : Set (PositiveRootIndex n)) vertex ⟨index, hindex⟩

end Schubert.DihedralSplines
