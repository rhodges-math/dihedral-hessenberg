import DihedralHessenberg.Dihedral.AlternatingWords

/-! # Distinct alternating products below the longest element

The two orientations have opposite modular coordinates. Equality would force
the nonzero expression length, which is less than n, to vanish modulo n.
-/

namespace Schubert.Dihedral

/-- The two alternating products of an intermediate length are distinct. -/
theorem alternatingWord_swap_ne (n : ℕ) (hthree : 3 ≤ n)
    (size : ℕ) (hpositive : 0 < size) (hshort : size < n) :
    (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 size) ≠
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 1 0 size) := by
  intro heq
  have hzero : (size : ZMod n) = 0 := by
    by_cases heven : Even size
    · have hparity := Nat.even_iff.mp heven
      have hsize : size = 2 * (size / 2) := by omega
      rw [hsize, alternatingWord_even_wordProd, alternatingWord_even_wordProd] at heq
      simp only [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, sub_zero, zero_sub,
        DihedralGroup.r_pow, one_mul, neg_mul, DihedralGroup.r.injEq] at heq
      rw [hsize]
      calc
        ((2 * (size / 2) : ℕ) : ZMod n) = (size / 2 : ℕ) + (size / 2 : ℕ) := by
          push_cast
          ring
        _ = -(size / 2 : ℕ) + (size / 2 : ℕ) :=
          congrArg (fun x : ZMod n => x + ((size / 2 : ℕ) : ZMod n)) heq
        _ = 0 := neg_add_cancel _
    · have hparity := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp heven)
      have hsize : size = 2 * (size / 2) + 1 := by omega
      rw [hsize, alternatingWord_odd_wordProd, alternatingWord_odd_wordProd] at heq
      simp only [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, sub_zero, zero_sub,
        DihedralGroup.r_pow, one_mul, neg_mul, DihedralGroup.r_mul_sr,
        DihedralGroup.sr.injEq, sub_neg_eq_add] at heq
      rw [hsize]
      calc
        ((2 * (size / 2) + 1 : ℕ) : ZMod n) =
            (1 + (size / 2 : ℕ)) + (size / 2 : ℕ) := by push_cast; ring
        _ = -(size / 2 : ℕ) + (size / 2 : ℕ) :=
          congrArg (fun x : ZMod n => x + ((size / 2 : ℕ) : ZMod n)) heq
        _ = 0 := neg_add_cancel _
  have hdiv := (ZMod.natCast_eq_zero_iff size n).mp hzero
  have := Nat.eq_zero_of_dvd_of_lt hdiv hshort
  omega

end Schubert.Dihedral
