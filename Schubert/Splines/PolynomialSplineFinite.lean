import Schubert.Splines.PolynomialGrading
import TauCeti.RingTheory.MvPolynomial.Finrank
import Mathlib.RingTheory.Noetherian.Basic

/-! # Unconditional finite homogeneous pieces on finite polynomial spline graphs -/

noncomputable section

namespace Schubert.Splines.IdealLabeledGraph

variable {K P V E : Type*} [CommRing K] [IsNoetherianRing K]
variable [Finite P] [Fintype V]
variable (graph : IdealLabeledGraph (MvPolynomial P K) V E)

/-- Over a Noetherian coefficient ring, each finite graph degree piece is finite. -/
theorem homogeneousPiece_finite (degree : ℕ) :
    Module.Finite K (graph.homogeneousPiece degree) := by
  let evaluation : graph.homogeneousPiece degree →ₗ[K]
      (V → MvPolynomial.homogeneousSubmodule P K degree) := {
    toFun := fun value vertex => ⟨(value.val : V → MvPolynomial P K) vertex,
      value.property vertex⟩
    map_add' := fun _ _ => by ext; rfl
    map_smul' := fun _ _ => by ext; rfl }
  apply Module.Finite.of_injective evaluation
  intro first second heq
  apply Subtype.ext
  apply Subtype.ext
  funext vertex
  exact congrArg Subtype.val (congrFun heq vertex)

end Schubert.Splines.IdealLabeledGraph
