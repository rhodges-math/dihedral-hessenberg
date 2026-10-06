import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.Data.Fintype.Sigma

/-! # Traces of module direct-sum representations -/

noncomputable section
open scoped DirectSum BigOperators
namespace Schubert.FiniteGroupCharacters

/-- The finite module direct-sum action has the sum of its factor characters. -/
theorem directSum_character {K J G : Type*} [Field K] [Monoid G] [Fintype J]
    {M : J → Type*} [∀ index, AddCommGroup (M index)] [∀ index, Module K (M index)]
    [∀ index, Module.Finite K (M index)]
    (actions : ∀ index, Representation K G (M index)) (element : G) :
    (Representation.directSum actions).character element =
      ∑ index, (actions index).character element := by
  classical
  let basis (index : J) := Module.Free.chooseBasis K (M index)
  let : ∀ index, Fintype (Module.Free.ChooseBasisIndex K (M index)) := fun index =>
    FiniteDimensional.fintypeBasisIndex (basis index)
  let totalBasis : Module.Basis
      (Σ index : J, Module.Free.ChooseBasisIndex K (M index)) K (⨁ index : J, M index) :=
    DFinsupp.basis basis
  change LinearMap.trace K _ ((Representation.directSum actions) element) = _
  rw [LinearMap.trace_eq_matrix_trace K totalBasis, Matrix.trace,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro index _
  change _ = LinearMap.trace K _ (actions index element)
  rw [LinearMap.trace_eq_matrix_trace K (basis index), Matrix.trace]
  apply Finset.sum_congr rfl
  intro vector _
  rw [Matrix.diag_apply, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp [totalBasis, DFinsupp.basis, Representation.directSum]
  change ((basis index).repr (actions index element
    ((DFinsupp.single index (basis index vector)) index))) vector = _
  rw [DFinsupp.single_eq_same]

end Schubert.FiniteGroupCharacters
