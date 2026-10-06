import Schubert.Splines.HomogeneousBasis
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Character

/-! # Characters in finite homogeneous coordinates -/

noncomputable section
open scoped BigOperators
namespace Schubert.FiniteGroupCharacters
open Schubert.Splines
variable {K G M I : Type*} [Field K] [Monoid G] [AddCommGroup M] [Module K M]
variable [Fintype I] (action : Representation K G M)
variable (pieces : ℕ → Subrepresentation action)
variable [DirectSum.Decomposition (fun d => (pieces d).toSubmodule)]
variable (basis : Module.Basis I K M) (degrees : I → ℕ)
variable (hbasis : ∀ i, basis i ∈ (pieces (degrees i)).toSubmodule)

/-- Restricted homogeneous coordinates agree with the basis coordinates. -/
theorem homogeneous_coordinate (degree : ℕ) (value : (pieces degree).toSubmodule)
    (index : {i // degrees i = degree}) :
    (homogeneousPieceBasis (fun d => (pieces d).toSubmodule) basis degrees hbasis degree).repr
      value index = basis.repr value.val index.val := by
  classical
  let localBasis := homogeneousPieceBasis (fun d => (pieces d).toSubmodule)
    basis degrees hbasis degree
  have expansion : value.val = ∑ j, localBasis.repr value j • basis j.val := by
    have h := congrArg Subtype.val (localBasis.sum_repr value)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, localBasis,
      homogeneousPieceBasis_apply] using h.symm
  rw [expansion, map_sum]
  simp [Finsupp.single_apply, Subtype.val_injective.eq_iff, localBasis]

include hbasis in
/-- Each homogeneous character is the diagonal sum over its basis fiber. -/
theorem homogeneous_character (degree : ℕ) (element : G) :
    letI := Module.Finite.of_basis
      (homogeneousPieceBasis (fun d => (pieces d).toSubmodule) basis degrees hbasis degree)
    ((pieces degree).toRepresentation).character element =
      ∑ index : {i // degrees i = degree},
        basis.repr (action element (basis index.val)) index.val :=
  by
  classical
  let localBasis := homogeneousPieceBasis (fun d => (pieces d).toSubmodule)
    basis degrees hbasis degree
  let := Module.Finite.of_basis localBasis
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K localBasis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro index _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [homogeneous_coordinate action pieces basis degrees hbasis degree]
  change basis.repr (action element
    (homogeneousPieceBasis (fun d => (pieces d).toSubmodule) basis degrees hbasis degree
      index : M)) index.val = _
  rw [homogeneousPieceBasis_apply]

include hbasis in
/-- The whole character is the sum of its bounded homogeneous characters. -/
theorem whole_homogeneous_character (top : ℕ) (hbound : ∀ i, degrees i ≤ top)
    (element : G) :
    letI := Module.Finite.of_basis basis
    letI := fun d => Module.Finite.of_basis
      (homogeneousPieceBasis (fun d => (pieces d).toSubmodule) basis degrees hbasis d)
    action.character element =
      ∑ degree ∈ Finset.range (top + 1), ((pieces degree).toRepresentation).character element := by
  classical
  let := Module.Finite.of_basis basis
  let := fun d => Module.Finite.of_basis
    (homogeneousPieceBasis (fun d => (pieces d).toSubmodule) basis degrees hbasis d)
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K basis, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.range (top + 1)) (g := degrees)
    (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound i)))]
  apply Finset.sum_congr rfl
  intro degree _
  rw [homogeneous_character action pieces basis degrees hbasis degree element]
  exact Finset.sum_subtype (Finset.univ.filter fun i => degrees i = degree)
    (fun i => by simp) (fun i => basis.repr (action element (basis i)) i)

end Schubert.FiniteGroupCharacters
