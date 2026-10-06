import Schubert.DihedralSplines.HessenbergInversions
import Schubert.Dihedral.NormalForms

/-! # Dominant simple roots of a Hessenberg space -/

namespace Schubert.Dihedral

/-- Reversing the alternating word makes its first generator the other simple generator. -/
theorem reverse_alternatingWord_starts_other (simple : Fin 2) (size : ℕ)
    (hpositive : 0 < size) :
    ∃ suffix : List (Fin 2),
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse = simple.rev :: suffix := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.reverse_concat]
  exact ⟨_, rfl⟩

/-- A bounded reversed alternating word has its stated canonical Coxeter length. -/
theorem length_reverse_alternatingWord (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2)
    (size : ℕ) (hbound : size ≤ n) :
    length n hthree ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse) = size := by
  have hne : simple ≠ simple.rev := by fin_cases simple <;> decide
  have hword := alternatingWord_isReduced n hthree simple simple.rev hne size hbound
  exact hword.reverse.eq.trans (by simp only [List.length_reverse,
    CoxeterSystem.length_alternatingWord])

end Schubert.Dihedral
namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A simple root is H-dominant when a reduced alternating word beginning with
 the other simple reflection has middle H-length and only its dominant simple edge. -/
noncomputable def IsDominant (ideal : HessenbergSpace n hthree) (simple : Fin 2) : Prop :=
  ∃ size : ℕ, 0 < size ∧ size ≤ n ∧
    let element := (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse
    ideal.length element = ideal.roots.card / 2 ∧
      (∃ index ∈ ideal.roots,
        simpleReflection n simple * element = element * rootReflection index) ∧
      ¬∃ index ∈ ideal.roots,
        simpleReflection n simple.rev * element = element * rootReflection index

/-- An H-dominant simple root has a bounded nonempty alternating witness with
 the paper's middle degree and the two prescribed simple-edge conditions. -/
theorem isDominant_iff (ideal : HessenbergSpace n hthree) (simple : Fin 2) :
    ideal.IsDominant simple ↔
      ∃ size : ℕ, 0 < size ∧ size ≤ n ∧
        let element := (coxeterSystem n hthree).wordProd
          (CoxeterSystem.alternatingWord simple simple.rev size).reverse
        ideal.length element = ideal.roots.card / 2 ∧
          (∃ index ∈ ideal.roots,
            simpleReflection n simple * element = element * rootReflection index) ∧
          ¬∃ index ∈ ideal.roots,
            simpleReflection n simple.rev * element = element * rootReflection index := Iff.rfl

end Schubert.DihedralSplines.HessenbergSpace
