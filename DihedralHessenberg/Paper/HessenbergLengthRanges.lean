import DihedralHessenberg.Paper.HessenbergDegreeThreshold
import DihedralHessenberg.Paper.HessenbergSymmetry
import DihedralHessenberg.Dihedral.LongestLength

/-! # Hessenberg length for even-sized root ideals -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- For an even-sized ideal, H-length agrees with canonical length below half,
 is constant in the middle, and has complementary canonical length above half. -/
theorem length_piecewise_of_even (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hcard : ideal.roots.card = 2 * half) (element : DihedralGroup n) :
    ideal.length element =
      if Schubert.Dihedral.length n hthree element ≤ half then
        Schubert.Dihedral.length n hthree element
      else if Schubert.Dihedral.length n hthree element < n - half then half
      else ideal.roots.card - (n - Schubert.Dihedral.length n hthree element) := by
  have hhalf : 2 * half ≤ ideal.roots.card := hcard.ge
  have hbound := length_le_polygon_parameter n hthree element
  have hmaximum := ideal.card_le
  let top := (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)
  have htopLength : Schubert.Dihedral.length n hthree (top * element) =
      n - Schubert.Dihedral.length n hthree element :=
    length_alternatingWord_top_mul n hthree element
  have hsum : ideal.length (top * element) + ideal.length element = ideal.roots.card :=
    ideal.length_alternatingWord_top_mul_add element
  by_cases hlow : Schubert.Dihedral.length n hthree element ≤ half
  · rw [ite_eq_left hlow]
    exact ideal.length_eq_coxeter_length_of_le_half half hhalf element hlow
  rw [ite_eq_right hlow]
  by_cases hmiddle : Schubert.Dihedral.length n hthree element < n - half
  · rw [ite_eq_left hmiddle]
    have hfirst := ideal.half_le_length_of_half_le_coxeter_length half hhalf element (by omega)
    have hsecond := ideal.half_le_length_of_half_le_coxeter_length half hhalf
      (top * element) (by omega)
    omega
  · rw [ite_eq_right hmiddle]
    have htopDegree := ideal.length_eq_coxeter_length_of_le_half half hhalf
      (top * element) (by omega)
    omega

/-- In the upper canonical range, H-length is the complementary canonical degree. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.LengthRanges.card_sub_complementary (ideal :
  HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (element : DihedralGroup n)
    (hupper : n - half ≤ Schubert.Dihedral.length n hthree element) :
    ideal.length element =
      ideal.roots.card - (n - Schubert.Dihedral.length n hthree element) := by
  let top := (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)
  have htopLength : Schubert.Dihedral.length n hthree (top * element) =
      n - Schubert.Dihedral.length n hthree element :=
    length_alternatingWord_top_mul n hthree element
  have htopDegree := ideal.length_eq_coxeter_length_of_le_half half hhalf
    (top * element) (by omega)
  have hsum : ideal.length (top * element) + ideal.length element = ideal.roots.card :=
    ideal.length_alternatingWord_top_mul_add element
  omega

/-- Between the two outer canonical ranges, an odd-sized ideal has only its two middle degrees. -/
theorem length_eq_half_or_half_add_one_of_odd (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hcard : ideal.roots.card = 2 * half + 1) (element : DihedralGroup n)
    (hlower : half ≤ Schubert.Dihedral.length n hthree element)
    (hupper : Schubert.Dihedral.length n hthree element ≤ n - half) :
    ideal.length element = half ∨ ideal.length element = half + 1 := by
  have hhalf : 2 * half ≤ ideal.roots.card := by omega
  let top := (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)
  have htopLength : Schubert.Dihedral.length n hthree (top * element) =
      n - Schubert.Dihedral.length n hthree element :=
    length_alternatingWord_top_mul n hthree element
  have hfirst := ideal.half_le_length_of_half_le_coxeter_length half hhalf element hlower
  have hsecond := ideal.half_le_length_of_half_le_coxeter_length half hhalf
    (top * element) (by omega)
  have hsum : ideal.length (top * element) + ideal.length element = ideal.roots.card :=
    ideal.length_alternatingWord_top_mul_add element
  omega
end Schubert.DihedralSplines.HessenbergSpace
