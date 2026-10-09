import DihedralHessenberg.Dihedral.CoinvariantPowerRelations

/-! # Multiplication relations in the dihedral coinvariant algebra

The two invariant generators vanish in the official quotient. Their axial consequences
are expressed directly using the quotient ring operations.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The two axial coordinate classes have zero product. -/
theorem coinvariant_auxiliary_mul (n : ℕ) [NeZero n] :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU *
      Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV = 0 := by
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (quadraticInvariant_mem_coinvariantIdeal n)
  simpa [quadraticInvariant] using hzero

/-- The higher invariant gives the signed relation between the top axial classes. -/
theorem coinvariant_top_relation (n : ℕ) [NeZero n] :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ n +
      Ideal.Quotient.mk (coinvariantIdeal n) (MvPolynomial.C ((-1 : ℂ) ^ n)) *
        Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ n = 0 := by
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (higherInvariant_mem_coinvariantIdeal n)
  simpa [higherInvariant] using hzero

/-- The first axial class vanishes in power n+1. -/
theorem coinvariant_auxiliaryU_pow_succ (n : ℕ) [NeZero n] :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ (n + 1) = 0 := by
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (auxiliaryU_pow_mem_coinvariantIdeal n)
  simpa using hzero

/-- The second axial class vanishes in power n+1. -/
theorem coinvariant_auxiliaryV_pow_succ (n : ℕ) [NeZero n] :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ (n + 1) = 0 := by
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (auxiliaryV_pow_mem_coinvariantIdeal n)
  simpa using hzero

end Schubert.Dihedral
