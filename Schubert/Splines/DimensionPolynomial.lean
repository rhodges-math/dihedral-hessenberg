import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Dimension polynomials of finite internally graded vector spaces -/

noncomputable section

namespace Schubert.Splines.Graded

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- Only finitely many subspaces in an internal direct sum can be nonzero. -/
theorem finite_pieces (pieces : ℕ → Submodule K V) (hinternal : DirectSum.IsInternal pieces) :
    Set.Finite {degree | pieces degree ≠ ⊥} :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep hinternal.submodule_iSupIndep

/-- The dimensions of internally graded pieces have finite support. -/
theorem finite_dimensions (pieces : ℕ → Submodule K V)
    (hinternal : DirectSum.IsInternal pieces) :
    (Function.support fun degree => Module.finrank K (pieces degree)).Finite := by
  apply (finite_pieces pieces hinternal).subset
  intro degree hdegree hzero
  apply hdegree
  simp [hzero]

/-- The polynomial whose coefficient in every degree is the dimension of that graded piece. -/
def dimensionPolynomial (pieces : ℕ → Submodule K V) (hinternal : DirectSum.IsInternal pieces) :
    Polynomial ℕ :=
  Polynomial.ofFinsupp ⟨Finsupp.ofSupportFinite
    (fun degree => Module.finrank K (pieces degree)) (finite_dimensions pieces hinternal)⟩

/-- Every coefficient records its graded dimension, without a degree cutoff. -/
theorem coeff (pieces : ℕ → Submodule K V) (hinternal : DirectSum.IsInternal pieces)
    (degree : ℕ) :
    (dimensionPolynomial pieces hinternal).coeff degree = Module.finrank K (pieces degree) := rfl

end Schubert.Splines.Graded
