import Schubert.Dihedral.Coxeter
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import TauCeti.GroupTheory.Coxeter.Bruhat

/-!
# Coxeter systems and indexed inversions for dihedral groups

The two-generator recognition theorem identifies the concrete dihedral group
with its rank-two Coxeter presentation. Length, reduced words, and Bruhat order
are the canonical Coxeter notions, and inversion sets use positive-root indices.
-/

namespace Schubert.Dihedral

/-- Each generator of the rank-two presentation is an involution. -/
theorem presentation_simple_mul_self (n : ℕ) (index : Fin 2) :
    (CoxeterMatrix.I (n - 2)).simple index * (CoxeterMatrix.I (n - 2)).simple index = 1 := by
  simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
    (CoxeterMatrix.I (n - 2)).toCoxeterSystem.simple_mul_simple_self index
theorem presentation_simple_ne_one (n : ℕ) (i : Fin 2) :
    (CoxeterMatrix.I (n - 2)).simple i ≠ 1 := by
  intro heq
  have hlength := (CoxeterMatrix.I (n - 2)).toCoxeterSystem.length_simple i
  rw [CoxeterMatrix.toCoxeterSystem_simple, heq,
    CoxeterSystem.length_one] at hlength
  exact Nat.zero_ne_one hlength

/-- The concrete dihedral group is isomorphic to its rank-two Coxeter presentation. -/
noncomputable def presentationEquiv (n : ℕ) (hthree : 3 ≤ n) :
    DihedralGroup n ≃* (CoxeterMatrix.I (n - 2)).Group :=
  TauCeti.dihedralGroupMulEquiv
    (presentation_simple_mul_self n 0)
    (presentation_simple_mul_self n 1)
    (presentation_simple_ne_one n 0) (presentation_simple_ne_one n 1)
    (orderOf_presentation_simple_mul_simple n hthree) (presentation_simple_generators n)

theorem presentationEquiv_firstSimpleReflection (n : ℕ) (hthree : 3 ≤ n) :
    presentationEquiv n hthree (firstSimpleReflection n) =
      (CoxeterMatrix.I (n - 2)).simple 0 := by
  rw [firstSimpleReflection, presentationEquiv, TauCeti.dihedralGroupMulEquiv_apply,
    TauCeti.dihedralHom_sr, ZMod.cast_zero, zpow_zero, mul_one]

theorem presentationEquiv_secondSimpleReflection (n : ℕ) (hthree : 3 ≤ n) :
    presentationEquiv n hthree (secondSimpleReflection n) =
      (CoxeterMatrix.I (n - 2)).simple 1 := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let : Fact (1 < n) := ⟨lt_of_lt_of_le (by decide : 1 < 3) hthree⟩
  have hcast : (ZMod.cast (1 : ZMod n) : ℤ) = 1 := by
    rw [ZMod.cast_eq_val, ZMod.val_one, Nat.cast_one]
  rw [secondSimpleReflection, presentationEquiv, TauCeti.dihedralGroupMulEquiv_apply,
    TauCeti.dihedralHom_sr, hcast, zpow_one, ← mul_assoc,
    presentation_simple_mul_self, one_mul]

/-- The Coxeter system of an `n`-gon on the concrete dihedral group. -/
noncomputable def coxeterSystem (n : ℕ) (hthree : 3 ≤ n) :
    CoxeterSystem (CoxeterMatrix.I (n - 2)) (DihedralGroup n) :=
  ⟨presentationEquiv n hthree⟩

/-- The Coxeter system's generators are the distinguished concrete reflections. -/
theorem coxeterSystem_simple (n : ℕ) (hthree : 3 ≤ n) (i : Fin 2) :
    (coxeterSystem n hthree).simple i = simpleReflection n i := by
  apply (presentationEquiv n hthree).injective
  change presentationEquiv n hthree
    ((presentationEquiv n hthree).symm ((CoxeterMatrix.I (n - 2)).simple i)) =
      presentationEquiv n hthree (simpleReflection n i)
  rw [MulEquiv.apply_symm_apply]
  fin_cases i
  · simpa [simpleReflection] using
      (presentationEquiv_firstSimpleReflection n hthree).symm
  · simpa [simpleReflection] using
      (presentationEquiv_secondSimpleReflection n hthree).symm

/-- The minimal length of an expression in the two distinguished simple reflections. -/
noncomputable def length (n : ℕ) (hthree : 3 ≤ n) (w : DihedralGroup n) : ℕ :=
  (coxeterSystem n hthree).length w

/-- A word in the two simple-reflection indices is reduced when it has minimal length. -/
def IsReduced (n : ℕ) (hthree : 3 ≤ n) (word : List (Fin 2)) : Prop :=
  (coxeterSystem n hthree).IsReduced word

/-- The strong Bruhat order, equivalently the subword relation on reduced expressions. -/
def BruhatLE (n : ℕ) (hthree : 3 ≤ n) (u v : DihedralGroup n) : Prop :=
  (coxeterSystem n hthree).BruhatLE u v

/-- The positive-root indices whose reflections lower length by left multiplication. -/
noncomputable def leftInversions (n : ℕ) (hthree : 3 ≤ n) (w : DihedralGroup n) :
    Finset (PositiveRootIndex n) := by
  classical
  exact Finset.univ.filter fun i => length n hthree (rootReflection i * w) < length n hthree w

/-- The positive-root indices whose reflections lower length by right multiplication. -/
noncomputable def rightInversions (n : ℕ) (hthree : 3 ≤ n) (w : DihedralGroup n) :
    Finset (PositiveRootIndex n) := by
  classical
  exact Finset.univ.filter fun i => length n hthree (w * rootReflection i) < length n hthree w

/-- The canonical Bruhat order has the subword characterization of a reduced expression. -/
theorem bruhatLE_iff_exists_sublist (n : ℕ) (hthree : 3 ≤ n) (u : DihedralGroup n)
    {word : List (Fin 2)} (hword : IsReduced n hthree word) :
    BruhatLE n hthree u ((coxeterSystem n hthree).wordProd word) ↔
      ∃ subword : List (Fin 2), subword.Sublist word ∧
        (coxeterSystem n hthree).wordProd subword = u :=
  (coxeterSystem n hthree).bruhatLE_iff_exists_sublist_wordProd_eq hword


/-- The identity has canonical Coxeter length zero. -/
@[simp] theorem length_one (n : ℕ) (hthree : 3 ≤ n) : length n hthree 1 = 0 :=
  (coxeterSystem n hthree).length_one

/-- Each distinguished simple reflection has canonical length one. -/
@[simp] theorem length_simpleReflection (n : ℕ) (hthree : 3 ≤ n) (index : Fin 2) :
    length n hthree (simpleReflection n index) = 1 := by
  change (coxeterSystem n hthree).length (simpleReflection n index) = 1
  rw [← coxeterSystem_simple n hthree index]
  exact (coxeterSystem n hthree).length_simple index

/-- Inversion preserves canonical Coxeter length. -/
theorem length_inv (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    length n hthree element⁻¹ = length n hthree element :=
  (coxeterSystem n hthree).length_inv element

/-- Reduced words attain the canonical minimum expression length. -/
theorem isReduced_iff_length_wordProd (n : ℕ) (hthree : 3 ≤ n) (word : List (Fin 2)) :
    IsReduced n hthree word ↔
      length n hthree ((coxeterSystem n hthree).wordProd word) = word.length := Iff.rfl

/-- Membership in left inversions is the strict left length-lowering condition. -/
@[simp] theorem mem_leftInversions (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    index ∈ leftInversions n hthree element ↔
      length n hthree (rootReflection index * element) < length n hthree element := by
  classical
  simp only [leftInversions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in right inversions is the strict right length-lowering condition. -/
@[simp] theorem mem_rightInversions (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    index ∈ rightInversions n hthree element ↔
      length n hthree (element * rootReflection index) < length n hthree element := by
  classical
  simp only [rightInversions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The canonical Bruhat relation is reflexive. -/
theorem bruhatLE_refl (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    BruhatLE n hthree element element := (coxeterSystem n hthree).bruhatLE_refl element

/-- Bruhat comparison does not decrease canonical length. -/
theorem bruhatLE_length_le (n : ℕ) (hthree : 3 ≤ n) {first second : DihedralGroup n}
    (hcomparison : BruhatLE n hthree first second) :
    length n hthree first ≤ length n hthree second :=
  CoxeterSystem.BruhatLE.length_le hcomparison

/-- Opposite canonical Bruhat comparisons force equality. -/
theorem bruhatLE_antisymm (n : ℕ) (hthree : 3 ≤ n) {first second : DihedralGroup n}
    (hforward : BruhatLE n hthree first second) (hbackward : BruhatLE n hthree second first) :
    first = second := CoxeterSystem.BruhatLE.antisymm hforward hbackward

end Schubert.Dihedral
