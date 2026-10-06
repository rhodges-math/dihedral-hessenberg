import Schubert.Splines.Untwist
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite spline modules over a Noetherian label ring -/

namespace Schubert.Splines

namespace IdealLabeledGraph

variable {R V E : Type*} [CommRing R] [IsNoetherianRing R] [Fintype V]

/-- A finite graph's spline module is finite over any Noetherian label ring. -/
theorem spline_finite (graph : IdealLabeledGraph R V E) : Module.Finite R graph.Spline :=
  Module.Finite.of_injective graph.splineAlgebra.val.toLinearMap Subtype.val_injective

end IdealLabeledGraph

namespace ReflectionGraphData

variable {K S W T : Type*} [CommRing K] [CommRing S] [Algebra K S]
variable [IsNoetherianRing S] [Group W] [Fintype W]
variable (data : ReflectionGraphData K S W T)

/-- The left scalar module is finite for finite vertices and a Noetherian label ring. -/
theorem leftSpline_finite (selected : Set T) : Module.Finite S (data.Spline selected) :=
  (data.reflectionGraph selected).spline_finite

/-- The right scalar module is finite by untwisting to a fixed-label finite graph. -/
theorem rightSpline_finite (selected : Set T) :
    letI := data.rightAlgebra selected
    Module.Finite S (data.Spline selected) := by
  let := data.rightAlgebra selected
  let := (data.fixedLabelGraph selected).spline_finite
  exact Module.Finite.equiv (data.rightUntwistLinearEquiv selected).symm

end ReflectionGraphData

end Schubert.Splines
