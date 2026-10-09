import DihedralHessenberg.Splines.ScalarEmbeddings
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Finsupp.Fintype

/-! # Infinite coefficient dimension when polynomial variables are present -/

namespace Schubert.Splines

variable {K P : Type*} [Field K] [Nonempty P]

/-- With at least one variable, the monomial basis has infinitely many indices. -/
theorem polynomial_not_moduleFinite : ¬Module.Finite K (MvPolynomial P K) := by
  intro hfinite
  let := hfinite
  exact Module.Finite.not_linearIndependent_of_infinite
    (MvPolynomial.basisMonomials P K) (MvPolynomial.basisMonomials P K).linearIndependent

namespace ReflectionGraphData

variable {W T : Type*} [Group W]
variable (data : ReflectionGraphData K (MvPolynomial P K) W T)

/-- Constant scalar splines force infinite coefficient dimension. -/
theorem spline_not_moduleFinite (selected : Set T) :
    ¬Module.Finite K (data.Spline selected) := by
  intro hfinite
  let := hfinite
  let := Module.Finite.of_injective (data.constantHom selected).toLinearMap
    (data.constantHom_injective selected)
  exact polynomial_not_moduleFinite (K := K) (P := P) inferInstance

end ReflectionGraphData

end Schubert.Splines
