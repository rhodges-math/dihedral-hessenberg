import Schubert.DihedralSplines.PaperQuotientAction
import Schubert.Dihedral.CoinvariantAction
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Constant coinvariants in the right spline quotient -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Constant and orbit splines coincide on invariant polynomials. -/
theorem invariant_constant (polynomial : CoordinatePolynomial)
    (hinvariant : polynomial ∈ invariantSubalgebra n) :
    selected.constantHom hthree polynomial = selected.orbitHom hthree polynomial := by
  apply Subtype.ext
  funext vertex
  exact ((mem_invariantSubalgebra n polynomial).mp hinvariant vertex).symm

/-- A polynomial with zero constant coefficient lies in the coordinate variable ideal. -/
theorem variableIdeal_of_zero (polynomial : CoordinatePolynomial)
    (hzero : polynomial.constantCoeff = 0) :
    polynomial ∈ MvPolynomial.idealOfVars (Fin 2) ℂ := by
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 2) ℂ)]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 polynomial).mpr
  intro exponent hdegree
  have hexponent : exponent = 0 :=
    (Finsupp.degree_eq_zero_iff exponent).mp (by omega)
  subst exponent
  exact hzero

/-- Positive invariants become zero under the constant map to the right quotient. -/
theorem positiveInvariant_zero (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial ∈ positiveInvariantPolynomials n) :
    Right.quotientMap selected hthree (selected.constantHom hthree polynomial) = 0 := by
  apply (Right.map_zero_iff selected hthree _).mpr
  rw [selected.invariant_constant hthree polynomial hpolynomial.1]
  exact Ideal.mem_map_of_mem (selected.orbitHom hthree).toRingHom
    (variableIdeal_of_zero polynomial hpolynomial.2)

/-- The invariant-generated ideal is killed by the constant quotient map. -/
theorem coinvariantIdeal_zero (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial ∈ coinvariantIdeal n) :
    Right.quotientMap selected hthree (selected.constantHom hthree polynomial) = 0 := by
  have hle : coinvariantIdeal n ≤ RingHom.ker
      ((Right.quotientMap selected hthree).comp (selected.constantHom hthree)).toRingHom := by
    apply Ideal.span_le.mpr
    intro value hvalue
    exact selected.positiveInvariant_zero hthree value hvalue
  exact hle hpolynomial

/-- The constant polynomial map factors through the coinvariant algebra. -/
def coinvariantMap : CoinvariantAlgebra n →ₐ[ℂ] Right.Quotient selected hthree :=
  Ideal.Quotient.liftₐ (coinvariantIdeal n)
    ((Right.quotientMap selected hthree).comp (selected.constantHom hthree))
    (fun polynomial hpolynomial => selected.coinvariantIdeal_zero hthree polynomial hpolynomial)

/-- The coinvariant map preserves polynomial representatives. -/
theorem coinvariantMap_mk (polynomial : CoordinatePolynomial) :
    selected.coinvariantMap hthree (Ideal.Quotient.mk (coinvariantIdeal n) polynomial) =
      Right.quotientMap selected hthree (selected.constantHom hthree polynomial) := rfl

/-- Dot translation of a constant spline acts on its coefficient polynomial. -/
theorem dot_constant (element : DihedralGroup n) (polynomial : CoordinatePolynomial) :
    selected.dot hthree element (selected.constantHom hthree polynomial) =
      selected.constantHom hthree (polynomialAction n element polynomial) := by
  apply Subtype.ext
  funext vertex
  rfl

/-- The factored coinvariant map intertwines the two quotient actions. -/
theorem coinvariantMap_equivariant (element : DihedralGroup n) (value : CoinvariantAlgebra n) :
    selected.coinvariantMap hthree (coinvariantAction n element value) =
      Right.dotEquiv selected hthree element (selected.coinvariantMap hthree value) := by
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
  change selected.coinvariantMap hthree (coinvariantActionEquiv n element
    (Ideal.Quotient.mk (coinvariantIdeal n) polynomial)) = _
  rw [coinvariantActionEquiv_mk, coinvariantMap_mk, coinvariantMap_mk, Right.dot_map,
    selected.dot_constant]
end Schubert.Dihedral.RootSubset
