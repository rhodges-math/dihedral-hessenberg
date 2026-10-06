import Mathlib.RingTheory.Regular.RegularSequence
import Schubert.Dihedral.CoinvariantIdeal
import Schubert.Dihedral.InvariantsBasic
import Schubert.Dihedral.InvariantRelPrime

/-! # Regularity of the basic invariant generators

Relative primeness gives divisibility cancellation by the higher invariant modulo
the quadratic invariant. Multiplication by the higher invariant on that quotient is injective.
-/

noncomputable section

open scoped Pointwise

namespace Schubert.Dihedral

/-- Divisibility by the quadratic invariant is unaffected by the higher invariant factor. -/
theorem _root_.Schubert.Dihedral.Invariants.F2.dvd_Fn_mul_iff (n : ℕ) (hpositive : 0 < n)
    (polynomial : CoordinatePolynomial) :
    quadraticInvariant ∣ higherInvariant n * polynomial ↔ quadraticInvariant ∣ polynomial :=
  ⟨(basicInvariants_isRelPrime n hpositive).dvd_of_dvd_mul_left,
    fun hdivides => dvd_mul_of_dvd_right hdivides _⟩

/-- The quadratic invariant acts injectively on the polynomial algebra. -/
theorem quadraticInvariant_isSMulRegular :
    IsSMulRegular CoordinatePolynomial quadraticInvariant := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro polynomial hequal
  exact (mul_eq_zero.mp hequal).resolve_left quadraticInvariant_ne_zero

/-- The higher invariant acts injectively modulo the quadratic invariant. -/
theorem _root_.Schubert.Dihedral.Invariants.Fn.regular_mod_F2 (n : ℕ) (hpositive : 0 < n) :
    IsSMulRegular
      (CoordinatePolynomial ⧸ (Ideal.span {quadraticInvariant}))
      (higherInvariant n) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem
    (Ideal.span {quadraticInvariant}) (higherInvariant n)).mpr
  intro polynomial hproduct
  change higherInvariant n * polynomial ∈ Ideal.span {quadraticInvariant} at hproduct
  change polynomial ∈ Ideal.span {quadraticInvariant}
  rw [Ideal.mem_span_singleton] at hproduct ⊢
  exact (_root_.Schubert.Dihedral.Invariants.F2.dvd_Fn_mul_iff n hpositive polynomial).mp hproduct

/-- The two basic invariants form a regular sequence on the polynomial algebra. -/
theorem basicInvariants_regularSequence (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    RingTheory.Sequence.IsRegular CoordinatePolynomial
      [quadraticInvariant, higherInvariant n] := by
  have hquotient : IsSMulRegular (QuotSMulTop quadraticInvariant CoordinatePolynomial)
      (higherInvariant n) := by
    have hsubmodule : (quadraticInvariant • ⊤ : Submodule CoordinatePolynomial
        CoordinatePolynomial) = Ideal.span {quadraticInvariant} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    exact (Submodule.quotEquivOfEq _ _ hsubmodule).isSMulRegular_congr
      (higherInvariant n) |>.mpr
        (_root_.Schubert.Dihedral.Invariants.Fn.regular_mod_F2 n (by omega))
  refine ⟨?_, ?_⟩
  · apply RingTheory.Sequence.IsWeaklyRegular.cons quadraticInvariant_isSMulRegular
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr hquotient
  · have hlist : Ideal.ofList [quadraticInvariant, higherInvariant n] =
        Ideal.span {quadraticInvariant, higherInvariant n} := by
      apply congrArg Ideal.span
      ext polynomial
      simp
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hlist,
      ← coinvariantIdeal_eq_span_basicInvariants n hthree]
    exact (coinvariantIdeal_ne_top n).symm
end Schubert.Dihedral




