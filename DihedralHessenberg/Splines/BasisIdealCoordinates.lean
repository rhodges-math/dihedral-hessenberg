import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Operations

/-! # Ideal multiples in basis coordinates

A basis identifies scalar-ideal multiples with vectors whose coordinates lie in
that ideal. This is the algebraic kernel needed to descend polynomial bases.
-/

namespace Schubert.Splines

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A vector is an ideal multiple precisely when every basis coordinate belongs to the ideal. -/
theorem mem_ideal_smul_top_iff_basis_coordinates
    (basis : Module.Basis I R M) (ideal : Ideal R) (value : M) :
    value ∈ ideal • (⊤ : Submodule R M) ↔ ∀ index, basis.repr value index ∈ ideal := by
  constructor
  · intro hvalue
    refine Submodule.smul_induction_on hvalue ?_ ?_
    · intro scalar hscalar vector _ index
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact ideal.mul_mem_right _ hscalar
    · intro first second hfirst hsecond index
      simpa only [map_add, Finsupp.add_apply] using ideal.add_mem (hfirst index) (hsecond index)
  · intro hcoordinates
    rw [← basis.linearCombination_repr value, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun index _ =>
      Submodule.smul_mem_smul (hcoordinates index) (Submodule.mem_top : basis index ∈ ⊤)

end Schubert.Splines
