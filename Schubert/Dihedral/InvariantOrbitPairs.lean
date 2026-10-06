import Lean.Elab.Tactic.Omega
import Schubert.Dihedral.InvariantPowerSums

/-! # Generation of rotation-resonant reflection pairs

The Newton power-sum formulas generate a reflection pair whenever the difference
of its auxiliary exponents is a multiple of the rotation order.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Reflection pairs with the first exponent larger belong to the basic invariant algebra. -/
theorem auxiliary_reflection_pair_mem_of_le (n first second : ℕ) (horder : second ≤ first)
    (hdivides : n ∣ first - second) :
    auxiliaryU ^ first * auxiliaryV ^ second +
        MvPolynomial.C ((-1 : ℂ) ^ (first + second)) *
          auxiliaryU ^ second * auxiliaryV ^ first ∈
      Algebra.adjoin ℂ ({quadraticInvariant, higherInvariant n} : Set CoordinatePolynomial) := by
  obtain ⟨degree, hdegree⟩ := hdivides
  have hfirst : first = n * degree + second := by omega
  have hexponent : first + second = n * degree + 2 * second := by omega
  have hsign : (-1 : ℂ) ^ (first + second) = (-1 : ℂ) ^ (n * degree) := by
    rw [hexponent, pow_add, pow_mul]
    norm_num
  rw [hsign, hfirst]
  exact _root_.Schubert.Dihedral.Invariants.mixed_pair_mem_adjoin n degree second

/-- Reflection pairs with the second exponent larger belong to the basic invariant algebra. -/
theorem auxiliary_reflection_pair_mem_of_ge (n first second : ℕ) (horder : first ≤ second)
    (hdivides : n ∣ second - first) :
    auxiliaryU ^ first * auxiliaryV ^ second +
        MvPolynomial.C ((-1 : ℂ) ^ (first + second)) *
          auxiliaryU ^ second * auxiliaryV ^ first ∈
      Algebra.adjoin ℂ ({quadraticInvariant, higherInvariant n} : Set CoordinatePolynomial) := by
  let sign : CoordinatePolynomial := MvPolynomial.C ((-1 : ℂ) ^ (first + second))
  have hsquare : sign ^ 2 = 1 := by
    dsimp [sign]
    rw [← map_pow, ← pow_mul, mul_comm (first + second), pow_mul]
    norm_num
  have hsign : sign ∈
      Algebra.adjoin ℂ ({quadraticInvariant, higherInvariant n} : Set CoordinatePolynomial) :=
    (Algebra.adjoin ℂ _).algebraMap_mem _
  have hpair := auxiliary_reflection_pair_mem_of_le n second first horder hdivides
  have hequal : auxiliaryU ^ first * auxiliaryV ^ second +
      MvPolynomial.C ((-1 : ℂ) ^ (first + second)) *
        auxiliaryU ^ second * auxiliaryV ^ first =
      sign * (auxiliaryU ^ second * auxiliaryV ^ first +
        MvPolynomial.C ((-1 : ℂ) ^ (second + first)) *
          auxiliaryU ^ first * auxiliaryV ^ second) := by
    rw [add_comm second first]
    change auxiliaryU ^ first * auxiliaryV ^ second +
      sign * auxiliaryU ^ second * auxiliaryV ^ first =
        sign * (auxiliaryU ^ second * auxiliaryV ^ first +
          sign * auxiliaryU ^ first * auxiliaryV ^ second)
    linear_combination -auxiliaryU ^ first * auxiliaryV ^ second * hsquare
  rw [hequal]
  exact (Algebra.adjoin ℂ _).mul_mem hsign hpair

end Schubert.Dihedral
