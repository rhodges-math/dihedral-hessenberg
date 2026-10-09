import Mathlib.LinearAlgebra.Basis.Basic

/-! # Minimality of basis generating sets

A subset of the indexed vectors of a basis spans the module exactly when it includes
every index. This gives the minimal-generating assertion for either spline scalar basis.
-/

namespace Schubert.Splines

universe u v w

variable {R : Type u} {M : Type v} {I : Type w}
variable [Semiring R] [Nontrivial R] [AddCommMonoid M] [Module R M]

/-- No proper indexed subset of a basis generates the whole module. -/
theorem basis_span_image_eq_top_iff (basis : Module.Basis I R M) (indices : Set I) :
    Submodule.span R (basis '' indices) = ⊤ ↔ indices = Set.univ := by
  rw [Submodule.eq_top_iff_forall_basis_mem basis]
  simp only [basis.self_mem_span_image, Set.eq_univ_iff_forall]

end Schubert.Splines
