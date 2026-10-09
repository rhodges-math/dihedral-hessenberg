import DihedralHessenberg.Dihedral.RootInversionSigns
import DihedralHessenberg.Dihedral.RankTwoEndpoints

/-! # Lengths of conjugated simple reflections -/

namespace Schubert.Dihedral

/-- Odd alternating expressions fold to their shorter odd distance around the dihedral cycle. -/
theorem length_odd_alternatingWord (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (hne : first ≠ second) (size : ℕ) (hsize : size < n) :
    length n hthree ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord first second (2 * size + 1))) =
        min (2 * size + 1) (2 * (n - size) - 1) := by
  let : NeZero n := ⟨by omega⟩
  fin_cases first <;> fin_cases second
  · exact (hne rfl).elim
  · rw [alternatingWord_odd_wordProd]
    change length n hthree
      ((simpleReflection n 1 * simpleReflection n 0) ^ size * simpleReflection n 1) = _
    rw [simpleReflection_one, simpleReflection_zero]
    simp only [firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_pow, DihedralGroup.r_mul_sr]
    by_cases hlast : size + 1 = n
    · have hcoordinate : (1 : ZMod n) - (0 - 1) * (size : ZMod n) = 0 := by
        have hcast := congrArg (fun value : ℕ => (value : ZMod n)) hlast
        push_cast at hcast
        simp only [ZMod.natCast_self] at hcast
        linear_combination hcast
      rw [hcoordinate, length_sr, ite_eq_left rfl, min_eq_right (by omega)]
      omega
    · have hcoordinate : (1 : ZMod n) - (0 - 1) * (size : ZMod n) = (size + 1 : ℕ) := by
        push_cast
        ring
      rw [hcoordinate, length_sr]
      have hbound : size + 1 < n := by omega
      have hnezero : ((size + 1 : ℕ) : ZMod n) ≠ 0 := by
        intro heq
        have hval := congrArg ZMod.val heq
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hbound, ZMod.val_zero] at hval
        omega
      rw [ite_eq_right hnezero, ZMod.val_natCast, Nat.mod_eq_of_lt hbound]
      congr 1
      omega
  · rw [alternatingWord_odd_wordProd]
    change length n hthree
      ((simpleReflection n 0 * simpleReflection n 1) ^ size * simpleReflection n 0) = _
    rw [simpleReflection_zero, simpleReflection_one]
    simp only [firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      zero_sub, DihedralGroup.r_pow, one_mul, DihedralGroup.r_mul_sr, sub_zero]
    rw [length_sr_neg]
    by_cases hzero : size = 0
    · subst size
      rw [Nat.cast_zero, ite_eq_left rfl]
      omega
    · have hnezero : (size : ZMod n) ≠ 0 := by
        intro heq
        have hval := congrArg ZMod.val heq
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsize, ZMod.val_zero] at hval
        exact hzero hval
      rw [ite_eq_right hnezero, ZMod.val_natCast, Nat.mod_eq_of_lt hsize]
  · exact (hne rfl).elim

/-- Conjugating the next alternating generator produces the odd alternating reflection word. -/
theorem conjugate_next_alternating_generator (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (hne : first ≠ second) (size : ℕ) :
    ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord first second size))⁻¹ *
        simpleReflection n (if Even size then second else first) *
          (coxeterSystem n hthree).wordProd
            (CoxeterSystem.alternatingWord first second size) =
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord first second (2 * size + 1)) := by
  by_cases heven : Even size
  · obtain ⟨half, heq⟩ := heven
    have hsize : size = 2 * half := by omega
    rw [hsize, ite_eq_left (by exact ⟨half, by omega⟩),
      alternatingWord_even_wordProd, alternatingWord_odd_wordProd]
    fin_cases first <;> fin_cases second
    all_goals try exact (hne rfl).elim
    all_goals simp [simpleReflection, firstSimpleReflection, secondSimpleReflection,
      DihedralGroup.sr_mul_sr, DihedralGroup.r_pow, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.inv_r]
    all_goals ring
  · have hsize : size = 2 * (size / 2) + 1 := by
      rw [Nat.even_iff] at heven
      omega
    have hodd : ¬Even (2 * (size / 2) + 1) := by rw [← hsize]; exact heven
    rw [hsize, ite_eq_right hodd, alternatingWord_odd_wordProd,
      alternatingWord_odd_wordProd]
    fin_cases first <;> fin_cases second
    all_goals try exact (hne rfl).elim
    all_goals simp [simpleReflection, firstSimpleReflection, secondSimpleReflection,
      DihedralGroup.sr_mul_sr, DihedralGroup.r_pow, DihedralGroup.r_mul_sr,
      DihedralGroup.inv_sr]
    all_goals ring

/-- Under a simple left ascent, the conjugate reflection has the shorter odd distance. -/
theorem _root_.Schubert.Dihedral.Reflections.Lengths.conjugate_ascent_min (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    length n hthree (element⁻¹ * simpleReflection n simple * element) =
      min (2 * length n hthree element + 1) (2 * (n - length n hthree element) - 1) := by
  by_cases hzero : length n hthree element = 0
  · have hone : element = 1 := (coxeterSystem n hthree).length_eq_zero_iff.mp hzero
    subst element
    simp only [inv_one, one_mul, mul_one, length_simpleReflection, length_one,
      mul_zero, zero_add, Nat.sub_zero]
    omega
  · have hpositive : 0 < length n hthree element := by omega
    have hshort : length n hthree element < n := by
      have hbound := length_le_polygon_parameter n hthree (simpleReflection n simple * element)
      omega
    obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree element
    let next := if Even (length n hthree element) then second else first
    have hnextWord : (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord first second (length n hthree element + 1)) =
          simpleReflection n next * element := by
      rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.wordProd_cons,
        coxeterSystem_simple, hprod]
    have hnextLength : length n hthree (simpleReflection n next * element) =
        length n hthree element + 1 := by
      rw [← hnextWord, length_alternatingWord n hthree first second hne _ (by omega)]
    obtain ⟨ascent, _, hunique⟩ :=
      existsUnique_simple_left_ascent n hthree element hpositive hshort
    have hsimple : simple = next := (hunique simple hascent).trans (hunique next hnextLength).symm
    calc
      length n hthree (element⁻¹ * simpleReflection n simple * element) =
        length n hthree (((coxeterSystem n hthree).wordProd
          (CoxeterSystem.alternatingWord first second (length n hthree element)))⁻¹ *
            simpleReflection n next * (coxeterSystem n hthree).wordProd
              (CoxeterSystem.alternatingWord first second (length n hthree element))) := by
                rw [hprod, hsimple]
      _ = _ := by
        rw [conjugate_next_alternating_generator n hthree first second hne,
          length_odd_alternatingWord n hthree first second hne _ hshort]

/-- A simple left ascent gives the two-branch conjugate-reflection length formula. -/
theorem length_conjugate_simple_of_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    length n hthree (element⁻¹ * simpleReflection n simple * element) =
      if 2 * length n hthree element + 1 ≤ n then 2 * length n hthree element + 1
        else 2 * (n - length n hthree element) - 1 := by
  have hbound := length_le_polygon_parameter n hthree (simpleReflection n simple * element)
  rw [_root_.Schubert.Dihedral.Reflections.Lengths.conjugate_ascent_min n hthree simple element
    hascent]
  split_ifs with hhalf
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega)]

/-- A simple left descent gives the two-branch conjugate-reflection length formula. -/
theorem length_conjugate_simple_of_left_descent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hdescent : length n hthree (simpleReflection n simple * element) + 1 =
      length n hthree element) :
    length n hthree (element⁻¹ * simpleReflection n simple * element) =
      if 2 * length n hthree element - 1 ≤ n then 2 * length n hthree element - 1
        else 2 * (n - length n hthree element) + 1 := by
  have hascent : length n hthree
      (simpleReflection n simple * (simpleReflection n simple * element)) =
        length n hthree (simpleReflection n simple * element) + 1 := by
    rw [← mul_assoc, simpleReflection_mul_self, one_mul, hdescent]
  have hformula := length_conjugate_simple_of_left_ascent n hthree simple
    (simpleReflection n simple * element) hascent
  have hconj : (simpleReflection n simple * element)⁻¹ * simpleReflection n simple *
      (simpleReflection n simple * element) = element⁻¹ * simpleReflection n simple * element := by
    group
  have hbound := length_le_polygon_parameter n hthree element
  have hfirst : 2 * length n hthree (simpleReflection n simple * element) + 1 =
      2 * length n hthree element - 1 := by omega
  have hsecond : 2 * (n - length n hthree (simpleReflection n simple * element)) - 1 =
      2 * (n - length n hthree element) + 1 := by omega
  rw [hconj, hfirst, hsecond] at hformula
  exact hformula

private theorem rootReflection_eq_conjugate_of_neighbor {n : ℕ}
    (simple : Fin 2) (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hneighbor : simpleReflection n simple * element = element * rootReflection index) :
    rootReflection index = element⁻¹ * simpleReflection n simple * element := by
  calc
    rootReflection index = element⁻¹ * (element * rootReflection index) := by group
    _ = element⁻¹ * (simpleReflection n simple * element) := by rw [← hneighbor]
    _ = _ := by group

/-- The reflection joining a simple Bruhat ascent has the conjugated length formula. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.length_at_simple_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hup : BruhatLE n hthree element (simpleReflection n simple * element))
    (hne : element ≠ simpleReflection n simple * element)
    (hneighbor : simpleReflection n simple * element = element * rootReflection index) :
    length n hthree (rootReflection index) =
      if 2 * length n hthree element + 1 ≤ n then 2 * length n hthree element + 1
        else 2 * (n - length n hthree element) - 1 := by
  have hstrict := ((bruhatLE_iff_eq_or_length_lt n hthree _ _).mp hup).resolve_left hne
  have hdichotomy := (coxeterSystem n hthree).length_simple_mul element simple
  rw [coxeterSystem_simple] at hdichotomy
  change length n hthree (simpleReflection n simple * element) = length n hthree element + 1 ∨
    length n hthree (simpleReflection n simple * element) + 1 = length n hthree element
      at hdichotomy
  have hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1 := by omega
  rw [rootReflection_eq_conjugate_of_neighbor simple element index hneighbor]
  exact length_conjugate_simple_of_left_ascent n hthree simple element hascent

/-- The reflection joining a simple Bruhat descent has the conjugated length formula. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.length_at_simple_descent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hdown : BruhatLE n hthree (simpleReflection n simple * element) element)
    (hne : simpleReflection n simple * element ≠ element)
    (hneighbor : simpleReflection n simple * element = element * rootReflection index) :
    length n hthree (rootReflection index) =
      if 2 * length n hthree element - 1 ≤ n then 2 * length n hthree element - 1
        else 2 * (n - length n hthree element) + 1 := by
  have hstrict := ((bruhatLE_iff_eq_or_length_lt n hthree _ _).mp hdown).resolve_left hne
  have hdichotomy := (coxeterSystem n hthree).length_simple_mul element simple
  rw [coxeterSystem_simple] at hdichotomy
  change length n hthree (simpleReflection n simple * element) = length n hthree element + 1 ∨
    length n hthree (simpleReflection n simple * element) + 1 = length n hthree element
      at hdichotomy
  have hdescent : length n hthree (simpleReflection n simple * element) + 1 =
      length n hthree element := by omega
  rw [rootReflection_eq_conjugate_of_neighbor simple element index hneighbor]
  exact length_conjugate_simple_of_left_descent n hthree simple element hdescent

end Schubert.Dihedral
