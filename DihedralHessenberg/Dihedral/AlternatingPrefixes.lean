import DihedralHessenberg.Dihedral.ReverseAlternatingWords

/-! # Prefixes of an alternating dihedral word -/

namespace Schubert.Dihedral

/-- The product of the alternating prefix beginning with the chosen simple reflection. -/
noncomputable def alternatingPrefixProduct (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (size : ℕ) : DihedralGroup n :=
  (coxeterSystem n hthree).wordProd
    (CoxeterSystem.alternatingWord simple.rev simple size).reverse

/-- A bounded alternating prefix has length equal to its number of letters. -/
theorem length_alternatingPrefixProduct (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (size : ℕ) (hbound : size ≤ n) :
    length n hthree (alternatingPrefixProduct n hthree simple size) = size := by
  have hne : simple.rev ≠ simple := by fin_cases simple <;> decide
  exact (alternatingWord_isReduced n hthree simple.rev simple hne size hbound).reverse.eq.trans
    (by simp only [List.length_reverse, CoxeterSystem.length_alternatingWord])

/-- Distinct bounded prefix lengths give distinct group elements. -/
theorem alternatingPrefixProduct_injective (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) :
    Function.Injective fun size : Fin (n + 1) =>
      alternatingPrefixProduct n hthree simple size.val := by
  intro first second heq
  have hlength := congrArg (length n hthree) heq
  rw [length_alternatingPrefixProduct n hthree simple first.val (by omega),
    length_alternatingPrefixProduct n hthree simple second.val (by omega)] at hlength
  exact Fin.ext hlength

/-- The even prefixes of the first alternating chain are positive rotations. -/
theorem alternatingPrefixProduct_zero_even (n : ℕ) (hthree : 3 ≤ n) (half : ℕ) :
    alternatingPrefixProduct n hthree 0 (2 * half) =
      DihedralGroup.r (half : ZMod n) := by
  unfold alternatingPrefixProduct
  rw [TauCeti.reverse_alternatingWord_two_mul, alternatingWord_even_wordProd]
  simp [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow]

/-- The odd prefixes of the first alternating chain are its indexed reflections. -/
theorem alternatingPrefixProduct_zero_odd (n : ℕ) (hthree : 3 ≤ n) (half : ℕ) :
    alternatingPrefixProduct n hthree 0 (2 * half + 1) =
      DihedralGroup.sr (-(half : ZMod n)) := by
  unfold alternatingPrefixProduct
  rw [CoxeterSystem.wordProd_reverse, alternatingWord_odd_wordProd]
  simp [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
    DihedralGroup.r_mul_sr, DihedralGroup.inv_sr]

/-- The even prefixes of the second alternating chain are negative rotations. -/
theorem alternatingPrefixProduct_one_even (n : ℕ) (hthree : 3 ≤ n) (half : ℕ) :
    alternatingPrefixProduct n hthree 1 (2 * half) =
      DihedralGroup.r (-(half : ZMod n)) := by
  unfold alternatingPrefixProduct
  rw [TauCeti.reverse_alternatingWord_two_mul, alternatingWord_even_wordProd]
  simp [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow]

/-- The odd prefixes of the second alternating chain are its indexed reflections. -/
theorem alternatingPrefixProduct_one_odd (n : ℕ) (hthree : 3 ≤ n) (half : ℕ) :
    alternatingPrefixProduct n hthree 1 (2 * half + 1) =
      DihedralGroup.sr ((half : ZMod n) + 1) := by
  unfold alternatingPrefixProduct
  rw [CoxeterSystem.wordProd_reverse, alternatingWord_odd_wordProd]
  simp [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
    DihedralGroup.r_mul_sr, DihedralGroup.inv_sr, add_comm]

/-- The last odd prefix is the reflection indexed by the selected endpoint root. -/
theorem _root_.Schubert.Dihedral.Alternating.prefix_odd_reflection (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) :
    alternatingPrefixProduct n hthree simple (2 * half + 1) = rootReflection endpoint := by
  fin_cases simple
  · change alternatingPrefixProduct n hthree 0 (2 * half + 1) = rootReflection endpoint
    have hval : endpoint.val = 2 * half := hvalue
    rw [alternatingPrefixProduct_zero_odd,
      rootReflection_eq_sr_of_even endpoint (by omega), hval]
    have hquot : 2 * half / 2 = half := by omega
    rw [hquot]
  · change alternatingPrefixProduct n hthree 1 (2 * half + 1) = rootReflection endpoint
    have hval : endpoint.val = 2 * half + 1 := hvalue
    rw [alternatingPrefixProduct_one_odd,
      rootReflection_eq_sr_of_odd endpoint (by omega), hval]
    have hquot : (2 * half + 1) / 2 = half := by omega
    rw [hquot]

end Schubert.Dihedral
