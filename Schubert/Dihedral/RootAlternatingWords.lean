import Schubert.Dihedral.SimpleRootObjects
import Schubert.Dihedral.CoxeterSystem

/-! # Alternating products of root reflections -/

namespace Schubert.Dihedral

private theorem alternating_map {A B : Type*} (function : A → B)
    (first second : A) (size : ℕ) :
    (CoxeterSystem.alternatingWord first second size).map function =
      CoxeterSystem.alternatingWord (function first) (function second) size := by
  induction size generalizing first second with
  | zero => rfl
  | succ size ih =>
    rw [CoxeterSystem.alternatingWord_succ, List.map_concat, ih,
      CoxeterSystem.alternatingWord_succ]

namespace PositiveRoot

/-- The product of an alternating root-reflection word beginning with the first vector. -/
noncomputable def alternatingProduct {n : ℕ} (first second : PositiveRoot n) (size : ℕ) :
    DihedralGroup n :=
  ((CoxeterSystem.alternatingWord second first size).reverse.map reflection).prod

/-- Evaluation of an alternating simple-root word agrees with the Coxeter word product. -/
theorem alternatingProduct_indexed (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2) (size : ℕ) :
    (simpleRoot n hthree simple.rev).alternatingProduct (simpleRoot n hthree simple) size =
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord simple simple.rev size).reverse := by
  unfold alternatingProduct CoxeterSystem.wordProd
  rw [← alternating_map (simpleRoot n hthree) simple simple.rev size]
  simp only [List.map_reverse, List.map_map, Function.comp_def, simpleRoot_reflection]
  have hgenerators : (coxeterSystem n hthree).simple = simpleReflection n :=
    funext (coxeterSystem_simple n hthree)
  rw [hgenerators]

end PositiveRoot

/-- The two simple vector roots are distinct. -/
theorem simpleRoot_ne (n : ℕ) (hthree : 3 ≤ n) :
    simpleRoot n hthree 0 ≠ simpleRoot n hthree 1 := by
  intro heq
  have hindices := congrArg (fun alpha : PositiveRoot n => alpha.index.val) heq
  simp only [simpleRoot_zero, simpleRoot_one, PositiveRoot.index_equiv,
    firstSimpleRootIndex, secondSimpleRootIndex, Fin.val_mk] at hindices
  omega

/-- The simple-vector enumeration is injective. -/
theorem simpleRoot_injective (n : ℕ) (hthree : 3 ≤ n) :
    Function.Injective (simpleRoot n hthree) := by
  intro first second heq
  fin_cases first <;> fin_cases second
  · rfl
  · exact (simpleRoot_ne n hthree heq).elim
  · exact (simpleRoot_ne n hthree heq.symm).elim
  · rfl

/-- Ordered pairs of distinct simple vectors are the two prescribed generator orientations. -/
theorem simple_pair_index {n : ℕ} {hthree : 3 ≤ n} (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) :
    ∃ simple : Fin 2, alpha = simpleRoot n hthree simple ∧
      beta = simpleRoot n hthree simple.rev := by
  rcases hpair with hfirst | hsecond
  · exact ⟨0, hfirst.1, hfirst.2⟩
  · exact ⟨1, hsecond.1, hsecond.2⟩

end Schubert.Dihedral
