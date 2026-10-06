import Schubert.DihedralSplines.PaperQuotientGrading
import Schubert.Splines.ReflectionNoetherian

/-! # Finite graded geometric coordinate quotients -/

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- The whole geometric left quotient is finite-dimensional without a triangular family. -/
theorem quotient_finite : Module.Finite ℂ (Quotient selected hthree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := (dihedralReflectionData n hthree).leftQuotient_finite selected.indices
  exact Module.Finite.equiv (backendEquiv selected hthree).symm.toLinearEquiv

/-- The quotient degree pieces form an internal direct sum. -/
theorem piece_isInternal : DirectSum.IsInternal (piece selected hthree) := by
  let := gradedAlgebra selected hthree
  exact DirectSum.Decomposition.isInternal (piece selected hthree)

end Left

namespace Right

/-- The whole geometric right quotient is finite-dimensional without a triangular family. -/
theorem quotient_finite : Module.Finite ℂ (Quotient selected hthree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := (dihedralReflectionData n hthree).rightQuotient_finite selected.indices
  exact Module.Finite.equiv (backendEquiv selected hthree).symm.toLinearEquiv

/-- The quotient degree pieces form an internal direct sum. -/
theorem piece_isInternal : DirectSum.IsInternal (piece selected hthree) := by
  let := gradedAlgebra selected hthree
  exact DirectSum.Decomposition.isInternal (piece selected hthree)

end Right

end Schubert.Dihedral.RootSubset
