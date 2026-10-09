import DihedralHessenberg.Dihedral.InvariantGeneration

/-! # Nilpotent auxiliary coordinates in the coinvariant quotient

The positive invariant relations force both auxiliary coordinates to vanish in power
n+1. These relations are stated for the official coinvariant ideal.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The parity scalar in the higher invariant has square one. -/
theorem higherInvariant_sign_sq (n : ℕ) :
    (MvPolynomial.C ((-1 : ℂ) ^ n) : CoordinatePolynomial) ^ 2 = 1 := by
  rw [← map_pow, ← pow_mul, mul_comm n, pow_mul]
  norm_num

/-- The first auxiliary coordinate to power n+1 lies in the coinvariant ideal. -/
theorem auxiliaryU_pow_mem_coinvariantIdeal (n : ℕ) [NeZero n] :
    auxiliaryU ^ (n + 1) ∈ coinvariantIdeal n := by
  have hpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hequal : auxiliaryU ^ (n + 1) =
      higherInvariant n * auxiliaryU -
        MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryV ^ (n - 1) * quadraticInvariant := by
    have hpower : auxiliaryV ^ n = auxiliaryV ^ (n - 1) * auxiliaryV := by
      calc
        auxiliaryV ^ n = auxiliaryV ^ (n - 1 + 1) := by congr 1; omega
        _ = _ := pow_succ _ _
    rw [higherInvariant, quadraticInvariant, pow_succ, hpower]
    ring
  rw [hequal]
  exact (coinvariantIdeal n).sub_mem
    ((coinvariantIdeal n).mul_mem_right _ (higherInvariant_mem_coinvariantIdeal n))
    ((coinvariantIdeal n).mul_mem_left _ (quadraticInvariant_mem_coinvariantIdeal n))

/-- The second auxiliary coordinate to power n+1 lies in the coinvariant ideal. -/
theorem auxiliaryV_pow_mem_coinvariantIdeal (n : ℕ) [NeZero n] :
    auxiliaryV ^ (n + 1) ∈ coinvariantIdeal n := by
  have hpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hequal : auxiliaryV ^ (n + 1) =
      MvPolynomial.C ((-1 : ℂ) ^ n) * higherInvariant n * auxiliaryV -
        MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryU ^ (n - 1) * quadraticInvariant := by
    have hsquare := higherInvariant_sign_sq n
    rw [higherInvariant, quadraticInvariant]
    have hpower : auxiliaryU ^ n = auxiliaryU ^ (n - 1) * auxiliaryU := by
      calc
        auxiliaryU ^ n = auxiliaryU ^ (n - 1 + 1) := by congr 1; omega
        _ = _ := pow_succ _ _
    rw [hpower, pow_succ]
    linear_combination -auxiliaryV ^ n * auxiliaryV * hsquare
  rw [hequal]
  exact (coinvariantIdeal n).sub_mem
    ((coinvariantIdeal n).mul_mem_right _
      ((coinvariantIdeal n).mul_mem_left _ (higherInvariant_mem_coinvariantIdeal n)))
    ((coinvariantIdeal n).mul_mem_left _ (quadraticInvariant_mem_coinvariantIdeal n))

end Schubert.Dihedral
