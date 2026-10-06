import Schubert.DihedralSplines.HessenbergVectorClassification
import Schubert.DihedralSplines.DominanceOdd
import Schubert.DihedralSplines.MiddleDominantClass
import Schubert.Dihedral.TerminalConjugacy
import Schubert.Dihedral.RootCard
import Mathlib.Tactic

/-! # Distinct left graded actions for the two odd-size ideals -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters

private theorem simple_coset_classes_ne {n : ℕ} [NeZero n]
    (hthree : 3 ≤ n) (heven : Even n) :
    (TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep :
      TauCeti.repRing ℂ (DihedralGroup n)) ≠
        TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep := by
  intro heq
  have hchar := congrArg (TauCeti.repRingCharacter ℂ (DihedralGroup n)) heq
  have hval := congrFun hchar (DihedralGroup.sr 0)
  simp only [TauCeti.repRingCharacter_of] at hval
  rw [PositiveRoot.cosetFDRep_character, PositiveRoot.cosetFDRep_character,
    PositiveRoot.coset_character_even _ heven, PositiveRoot.coset_character_even _ heven]
    at hval
  have hfirst : (simpleRoot n hthree 0).reflection = DihedralGroup.sr 0 := by
    rw [simpleRoot_reflection, simpleReflection_zero]
    rfl
  have hself : IsConj (DihedralGroup.sr 0) (simpleRoot n hthree 0).reflection := by
    rw [hfirst]
  have hother : ¬IsConj (DihedralGroup.sr 0) (simpleRoot n hthree 1).reflection := by
    rw [← hfirst]
    exact simple_not_isConj n hthree heven
  rw [ite_eq_left hself, ite_eq_right hother] at hval
  norm_num at hval

private theorem different_dominants {n : ℕ} {hthree : 3 ≤ n} (heven : Even n)
    (first second : HessenbergIdeal n hthree) (half : ℕ)
    (hfirst : first.carrier.ncard = 2 * half + 1)
    (hsecond : second.carrier.ncard = 2 * half + 1)
    (hproperFirst : first.carrier ≠ positiveRoots n)
    (hproperSecond : second.carrier ≠ positiveRoots n)
    (hdomFirst : first.IsDominant (simpleRoot n hthree 0))
    (hdomSecond : second.IsDominant (simpleRoot n hthree 1)) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep first.toRootSubset hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) ≠
        TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep second.toRootSubset hthree half) := by
  let : NeZero n := ⟨by omega⟩
  intro heq
  rw [Left.middle_class_dominant first half hfirst hproperFirst _ hdomFirst,
    Left.middle_class_dominant second half hsecond hproperSecond _ hdomSecond] at heq
  apply simple_coset_classes_ne hthree heven
  simpa only [sub_left_inj, add_right_inj] using heq

private theorem literal_middle_ne {n : ℕ} {hthree : 3 ≤ n} (heven : Even n)
    (half : ℕ) (hbound : 2 * half + 1 < n) (first second : HessenbergIdeal n hthree)
    (hcardFirst : first.carrier.ncard = 2 * half + 1)
    (hcardSecond : second.carrier.ncard = 2 * half + 1)
    (hfirst : first.carrier = positiveRoot n '' {index : Fin n | index.val < 2 * half + 1})
    (hsecond : second.carrier = positiveRoot n ''
      {index : Fin n | index.val < 2 * half ∨ index.val = 2 * half + 1}) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep first.toRootSubset hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) ≠
        TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep second.toRootSubset hthree half) := by
  have hmemFirst (index : Fin n) :
      (positiveRootEquiv n index).val ∈ first ↔ index.val < 2 * half + 1 := by
    change positiveRoot n index ∈ first.carrier ↔ _
    rw [hfirst]
    simp only [Set.mem_image, Set.mem_ofPred_eq, (positiveRoot_injective n).eq_iff,
      exists_eq_right]
  have hmemSecond (index : Fin n) :
      (positiveRootEquiv n index).val ∈ second ↔
        index.val < 2 * half ∨ index.val = 2 * half + 1 := by
    change positiveRoot n index ∈ second.carrier ↔ _
    rw [hsecond]
    simp only [Set.mem_image, Set.mem_ofPred_eq, (positiveRoot_injective n).eq_iff,
      exists_eq_right]
  have hproperFirst : first.carrier ≠ positiveRoots n := by
    intro heq
    rw [heq, positiveRoots_ncard] at hcardFirst
    omega
  have hproperSecond : second.carrier ≠ positiveRoots n := by
    intro heq
    rw [heq, positiveRoots_ncard] at hcardSecond
    omega
  by_cases hparity : Even (n - half - 1)
  · have hdomFirst : first.IsDominant (simpleRoot n hthree 1) := by
      rw [dominant_second_iff first half hcardFirst hproperFirst, ite_eq_left hparity,
        hmemFirst]
      change 2 * half < 2 * half + 1
      omega
    have hdomSecond : second.IsDominant (simpleRoot n hthree 0) := by
      rw [dominant_first_iff second half hcardSecond hproperSecond, ite_eq_left hparity,
        hmemSecond]
      right
      rfl
    exact Ne.symm (different_dominants heven second first half hcardSecond hcardFirst
      hproperSecond hproperFirst hdomSecond hdomFirst)
  · have hdomFirst : first.IsDominant (simpleRoot n hthree 0) := by
      rw [dominant_first_iff first half hcardFirst hproperFirst, ite_eq_right hparity,
        hmemFirst]
      change 2 * half < 2 * half + 1
      omega
    have hdomSecond : second.IsDominant (simpleRoot n hthree 1) := by
      rw [dominant_second_iff second half hcardSecond hproperSecond, ite_eq_right hparity,
        hmemSecond]
      right
      rfl
    exact different_dominants heven first second half hcardFirst hcardSecond
      hproperFirst hproperSecond hdomFirst hdomSecond

/-- The two proper odd-size ideals have different left degree
and graded actions. -/
theorem odd_choices (n : ℕ) (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hpositive : 1 ≤ half) (hbound : 2 * half + 1 < n) :
    ∃ first second : HessenbergIdeal n hthree,
      first.carrier = positiveRoot n '' {index : Fin n | index.val < 2 * half + 1} ∧
      second.carrier = positiveRoot n ''
        {index : Fin n | index.val < 2 * half ∨ index.val = 2 * half + 1} ∧
      first.carrier.ncard = 2 * half + 1 ∧ second.carrier.ncard = 2 * half + 1 ∧
      ¬Nonempty (RootSubset.Left.pieceFDRep first.toRootSubset hthree half ≅
        RootSubset.Left.pieceFDRep second.toRootSubset hthree half) ∧
      RootSubset.Left.gradedClass first.toRootSubset hthree ≠
        RootSubset.Left.gradedClass second.toRootSubset hthree ∧
      ¬(∀ degree, Nonempty
        (RootSubset.Left.gradedRepresentation first.toRootSubset hthree degree ≅
          RootSubset.Left.gradedRepresentation second.toRootSubset hthree degree)) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨first, hcardFirst, hfirst⟩ := exists_initial n hthree (2 * half + 1)
    (by omega) (by omega)
  obtain ⟨second, hcardSecond, hsecond⟩ := exists_other n hthree (half + 1)
    (by omega) (by have := Nat.even_iff.mp heven; omega)
  have hsize : 2 * (half + 1) - 1 = 2 * half + 1 := by omega
  have hprevious : 2 * (half + 1) - 2 = 2 * half := by omega
  rw [hsize] at hcardSecond
  rw [hsize, hprevious] at hsecond
  have hclass := literal_middle_ne heven half hbound first second hcardFirst hcardSecond
    hfirst hsecond
  have hiso : ¬Nonempty (RootSubset.Left.pieceFDRep first.toRootSubset hthree half ≅
      RootSubset.Left.pieceFDRep second.toRootSubset hthree half) := by
    rintro ⟨isomorphism⟩
    exact hclass (TauCeti.SplitK0.of_congr isomorphism)
  have hgraded : RootSubset.Left.gradedClass first.toRootSubset hthree ≠
      RootSubset.Left.gradedClass second.toRootSubset hthree := by
    intro heq
    apply hclass
    simpa only [RootSubset.Left.gradedClass_coeff] using congrArg (PowerSeries.coeff half) heq
  refine ⟨first, second, hfirst, hsecond, hcardFirst, hcardSecond, hiso, hgraded, ?_⟩
  intro hfamily
  exact hgraded ((gradedClass_eq_iff_iso _ _).mpr hfamily)

/-- Any two ideals with the displayed odd-size carriers have different
left graded actions. -/
theorem odd_choice (n : ℕ) (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hpositive : 1 ≤ half) (hbound : 2 * half + 1 < n)
    (first second : HessenbergIdeal n hthree)
    (hfirst : first.carrier = positiveRoot n '' {index : Fin n | index.val < 2 * half + 1})
    (hsecond : second.carrier = positiveRoot n ''
      {index : Fin n | index.val < 2 * half ∨ index.val = 2 * half + 1}) :
    ¬Nonempty (RootSubset.Left.pieceFDRep first.toRootSubset hthree half ≅
      RootSubset.Left.pieceFDRep second.toRootSubset hthree half) ∧
    RootSubset.Left.gradedClass first.toRootSubset hthree ≠
      RootSubset.Left.gradedClass second.toRootSubset hthree ∧
    ¬(∀ degree, Nonempty
      (RootSubset.Left.gradedRepresentation first.toRootSubset hthree degree ≅
        RootSubset.Left.gradedRepresentation second.toRootSubset hthree degree)) := by
  obtain ⟨first', second', hfirst', hsecond', _, _, hiso, hgraded, hfamily⟩ :=
    odd_choices n hthree heven half hpositive hbound
  have heqFirst : first = first' := by
    apply SetLike.coe_injective
    change first.carrier = first'.carrier
    rw [hfirst, hfirst']
  have heqSecond : second = second' := by
    apply SetLike.coe_injective
    change second.carrier = second'.carrier
    rw [hsecond, hsecond']
  rw [heqFirst, heqSecond]
  exact ⟨hiso, hgraded, hfamily⟩

end Schubert.DihedralSplines.HessenbergIdeal
