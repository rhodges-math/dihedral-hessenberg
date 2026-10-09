import DihedralHessenberg.Dihedral.AlternatingWords

/-! # Conjugated simple reflections for reversed alternating products -/

namespace Schubert.Dihedral

/-- Conjugating the ascent generator of a reversed alternating product gives its sr form. -/
theorem conjugate_simple_reverse_alternatingWord (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (size : ℕ) :
    let element := (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse
    element⁻¹ * simpleReflection n simple * element =
      DihedralGroup.sr (if Even size then
        if simple = 0 then -(size : ZMod n) else (size : ZMod n) + 1
      else if simple = 0 then (size : ZMod n) + 1 else -(size : ZMod n)) := by
  dsimp only
  rw [CoxeterSystem.wordProd_reverse, inv_inv]
  by_cases heven : Even size
  · obtain ⟨half, hsize⟩ := heven
    have hvalue : size = 2 * half := by omega
    rw [hvalue, ite_eq_left (show Even (2 * half) from ⟨half, by omega⟩),
      alternatingWord_even_wordProd]
    fin_cases simple
    all_goals simp [Fin.rev, simpleReflection, firstSimpleReflection, secondSimpleReflection,
      DihedralGroup.sr_mul_sr, DihedralGroup.r_pow, DihedralGroup.inv_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    all_goals ring
  · have hvalue : size = 2 * (size / 2) + 1 := by rw [Nat.even_iff] at heven; omega
    rw [ite_eq_right heven, hvalue, alternatingWord_odd_wordProd]
    fin_cases simple
    all_goals simp [Fin.rev, simpleReflection, firstSimpleReflection, secondSimpleReflection,
      DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr]
    all_goals ring

/-- Conjugating the descent generator of a reversed alternating product gives its sr form. -/
theorem _root_.Schubert.Dihedral.Alternating.conjugate_other_reverse (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (size : ℕ) :
    let element := (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse
    element⁻¹ * simpleReflection n simple.rev * element =
      DihedralGroup.sr (if Even size then
        if simple = 0 then 1 - (size : ZMod n) else (size : ZMod n)
      else if simple = 0 then (size : ZMod n) else 1 - (size : ZMod n)) := by
  dsimp only
  rw [CoxeterSystem.wordProd_reverse, inv_inv]
  by_cases heven : Even size
  · obtain ⟨half, hsize⟩ := heven
    have hvalue : size = 2 * half := by omega
    rw [hvalue, ite_eq_left (show Even (2 * half) from ⟨half, by omega⟩),
      alternatingWord_even_wordProd]
    fin_cases simple
    all_goals simp [Fin.rev, simpleReflection, firstSimpleReflection, secondSimpleReflection,
      DihedralGroup.sr_mul_sr, DihedralGroup.r_pow, DihedralGroup.inv_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    all_goals ring
  · have hvalue : size = 2 * (size / 2) + 1 := by rw [Nat.even_iff] at heven; omega
    rw [ite_eq_right heven, hvalue, alternatingWord_odd_wordProd]
    fin_cases simple
    all_goals simp [Fin.rev, simpleReflection, firstSimpleReflection, secondSimpleReflection,
      DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr]
    all_goals ring

end Schubert.Dihedral
