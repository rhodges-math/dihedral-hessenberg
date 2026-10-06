import Schubert.DihedralSplines.OddIdealChoice
import Schubert.DihedralSplines.WholeQuotientCharacter
import Schubert.DihedralSplines.LeftOddDegreeClass

/-! # Distinct whole left actions for the two odd-size ideals -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters

private theorem degree_from_middle {n : ℕ} [NeZero n] {hthree : 3 ≤ n}
    (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : ℕ) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      (if degree = 0 ∨ degree = 2 * half + 1 then 1 else
        if degree < 2 * half + 1 then 2 else 0) +
      if degree = half ∨ degree = half + 1 then
        TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) - 2
      else 0 := by
  obtain ⟨alpha, ⟨_, hdominant⟩, _⟩ := dominant_odd_unique ideal half hcard hproper
  rw [Left.piece_class_odd ideal half hcard hproper alpha hdominant degree,
    Left.middle_class_dominant ideal half hcard hproper alpha hdominant, trivial_class_one]
  split_ifs <;> simp only [two_nsmul, one_add_one_eq_two]
  all_goals abel

private theorem whole_from_middle {n : ℕ} [NeZero n] {hthree : 3 ≤ n}
    (ideal : HessenbergIdeal n hthree) (half : ℕ) (hpositive : 1 ≤ half)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    (TauCeti.SplitK0.of (Left.wholeFDRep ideal) : TauCeti.repRing ℂ (DihedralGroup n)) =
      (∑ degree ∈ Finset.range (2 * half + 2),
        if degree = 0 ∨ degree = 2 * half + 1 then 1 else
          if degree < 2 * half + 1 then 2 else 0) +
      2 • (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) - 2) :=
    by
  rw [Left.whole_class, hcard]
  conv_lhs =>
    arg 2
    intro degree
    rw [degree_from_middle ideal half hcard hproper]
  rw [Finset.sum_add_distrib]
  congr 1
  let correction : TauCeti.repRing ℂ (DihedralGroup n) :=
    TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) - 2
  have split (degree : ℕ) :
      (if degree = half ∨ degree = half + 1 then correction else 0) =
        (if degree = half then correction else 0) +
        (if degree = half + 1 then correction else 0) := by
    split_ifs <;> try omega
    all_goals abel
  change (∑ degree ∈ Finset.range (2 * half + 1 + 1),
    if degree = half ∨ degree = half + 1 then correction else 0) = 2 • correction
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, show half < 2 * half + 1 + 1 by omega,
    show half + 1 < 2 * half + 1 + 1 by omega, ite_true, two_nsmul]

private theorem middle_iso_of_whole {n : ℕ} [NeZero n] {hthree : 3 ≤ n}
    (first second : HessenbergIdeal n hthree) (half : ℕ) (hpositive : 1 ≤ half)
    (hfirst : first.carrier.ncard = 2 * half + 1)
    (hsecond : second.carrier.ncard = 2 * half + 1)
    (hproperFirst : first.carrier ≠ positiveRoots n)
    (hproperSecond : second.carrier ≠ positiveRoots n)
    (isomorphism : Left.wholeFDRep first ≅ Left.wholeFDRep second) :
    Nonempty (RootSubset.Left.pieceFDRep first.toRootSubset hthree half ≅
      RootSubset.Left.pieceFDRep second.toRootSubset hthree half) := by
  have heq := TauCeti.SplitK0.of_congr isomorphism
  rw [whole_from_middle first half hpositive hfirst hproperFirst,
    whole_from_middle second half hpositive hsecond hproperSecond] at heq
  have hcorrection := add_left_cancel heq
  have hchar := congrArg (TauCeti.repRingCharacter ℂ (DihedralGroup n)) hcorrection
  simp only [map_nsmul, map_sub, TauCeti.repRingCharacter_of] at hchar
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  have hvalue := congrFun hchar element
  simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Nat.cast_ofNat] at hvalue
  linear_combination (1 / 2 : ℂ) * hvalue

/-- The two displayed odd-size ideals also have nonisomorphic whole left actions. -/
theorem odd_choice_whole (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hpositive : 1 ≤ half) (hbound : 2 * half + 1 < n)
    (first second : HessenbergIdeal n hthree)
    (hfirst : first.carrier = positiveRoot n '' {index : Fin n | index.val < 2 * half + 1})
    (hsecond : second.carrier = positiveRoot n ''
      {index : Fin n | index.val < 2 * half ∨ index.val = 2 * half + 1}) :
    ¬Nonempty (Left.wholeFDRep first ≅ Left.wholeFDRep second) := by
  obtain ⟨first', second', hfirst', hsecond', hcardFirst, hcardSecond, hmiddle, _, _⟩ :=
    odd_choices n hthree heven half hpositive hbound
  have heqFirst : first = first' := by
    apply SetLike.coe_injective
    change first.carrier = first'.carrier
    rw [hfirst, hfirst']
  have heqSecond : second = second' := by
    apply SetLike.coe_injective
    change second.carrier = second'.carrier
    rw [hsecond, hsecond']
  subst first
  subst second
  have hproperFirst : first'.carrier ≠ positiveRoots n := by
    intro heq
    rw [heq, positiveRoots_ncard] at hcardFirst
    omega
  have hproperSecond : second'.carrier ≠ positiveRoots n := by
    intro heq
    rw [heq, positiveRoots_ncard] at hcardSecond
    omega
  rintro ⟨isomorphism⟩
  exact hmiddle (middle_iso_of_whole first' second' half hpositive hcardFirst hcardSecond
    hproperFirst hproperSecond isomorphism)

/-- The two odd-size ideals have distinct whole left representations. -/
theorem odd_choices_whole (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hpositive : 1 ≤ half) (hbound : 2 * half + 1 < n) :
    ∃ first second : HessenbergIdeal n hthree,
      first.carrier = positiveRoot n '' {index : Fin n | index.val < 2 * half + 1} ∧
      second.carrier = positiveRoot n ''
        {index : Fin n | index.val < 2 * half ∨ index.val = 2 * half + 1} ∧
      first.carrier.ncard = 2 * half + 1 ∧ second.carrier.ncard = 2 * half + 1 ∧
      ¬Nonempty (Left.wholeFDRep first ≅ Left.wholeFDRep second) := by
  obtain ⟨first, second, hfirst, hsecond, hcardFirst, hcardSecond, _, _, _⟩ :=
    odd_choices n hthree heven half hpositive hbound
  exact ⟨first, second, hfirst, hsecond, hcardFirst, hcardSecond,
    odd_choice_whole n hthree heven half hpositive hbound first second hfirst hsecond⟩

end Schubert.DihedralSplines.HessenbergIdeal
