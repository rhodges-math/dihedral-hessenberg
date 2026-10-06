import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Card
import Schubert.DihedralSplines.Hessenberg

/-! # Basic properties of Hessenberg ideals

The real cone relation is reflexive and transitive. Hessenberg ideals are determined by their
root sets; the full positive-root set and intersections are again Hessenberg ideals.
-/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- A positive root differs from itself by the zero vector in the simple-root cone. -/
theorem rootLE_refl (n : ℕ) (hthree : 3 ≤ n) (index : PositiveRootIndex n) :
    RootLE n hthree index index := by
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  simp only [sub_self, zero_smul, add_zero]

/-- Comparison by the nonnegative simple-root cone is transitive. -/
theorem rootLE_trans {n : ℕ} {hthree : 3 ≤ n} {first second third : PositiveRootIndex n}
    (hfirst : RootLE n hthree first second) (hsecond : RootLE n hthree second third) :
    RootLE n hthree first third := by
  obtain ⟨a, b, ha, hb, hfirst⟩ := hfirst
  obtain ⟨c, d, hc, hd, hsecond⟩ := hsecond
  refine ⟨a + c, b + d, add_nonneg ha hc, add_nonneg hb hd, ?_⟩
  calc
    positiveRoot n third - positiveRoot n first =
        (positiveRoot n second - positiveRoot n first) +
          (positiveRoot n third - positiveRoot n second) := by abel
    _ = (a • positiveRoot n (firstSimpleRootIndex n hthree) +
          b • positiveRoot n (secondSimpleRootIndex n hthree)) +
        (c • positiveRoot n (firstSimpleRootIndex n hthree) +
          d • positiveRoot n (secondSimpleRootIndex n hthree)) := by rw [hfirst, hsecond]
    _ = _ := by simp only [add_smul]; abel

namespace HessenbergSpace

/-- Hessenberg ideals with the same root set are equal. -/
@[ext] theorem ext {n : ℕ} {hthree : 3 ≤ n} {first second : HessenbergSpace n hthree}
    (hroots : first.roots = second.roots) : first = second := by
  cases first
  cases second
  cases hroots
  rfl

/-- The full set of positive roots is a Hessenberg ideal. -/
def full (n : ℕ) (hthree : 3 ≤ n) : HessenbergSpace n hthree where
  roots := Finset.univ
  lower := fun _ _ _ _ => Finset.mem_univ _
  first_mem := Finset.mem_univ _
  second_mem := Finset.mem_univ _

/-- The intersection of two Hessenberg ideals is a Hessenberg ideal. -/
def inter {n : ℕ} {hthree : 3 ≤ n} (first second : HessenbergSpace n hthree) :
    HessenbergSpace n hthree where
  roots := first.roots ∩ second.roots
  lower := by
    intro smaller larger hrelation hmem
    obtain ⟨hfirst, hsecond⟩ := Finset.mem_inter.mp hmem
    exact Finset.mem_inter.mpr ⟨first.lower hrelation hfirst, second.lower hrelation hsecond⟩
  first_mem := Finset.mem_inter.mpr ⟨first.first_mem, second.first_mem⟩
  second_mem := Finset.mem_inter.mpr ⟨first.second_mem, second.second_mem⟩

/-- Every positive root belongs to the full Hessenberg ideal. -/
@[simp] theorem mem_full (n : ℕ) (hthree : 3 ≤ n) (index : PositiveRootIndex n) :
    index ∈ (full n hthree).roots := Finset.mem_univ _

/-- Membership in the intersection is membership in both Hessenberg ideals. -/
@[simp] theorem mem_inter {n : ℕ} {hthree : 3 ≤ n} (first second : HessenbergSpace n hthree)
    (index : PositiveRootIndex n) :
    index ∈ (inter first second).roots ↔ index ∈ first.roots ∧ index ∈ second.roots :=
  Finset.mem_inter

/-- Every Hessenberg ideal contains at least the two distinct simple roots. -/
theorem two_le_card {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree) :
    2 ≤ ideal.roots.card := by
  have hdistinct : firstSimpleRootIndex n hthree ≠ secondSimpleRootIndex n hthree := by
    intro heq
    have hvalues := congrArg Fin.val heq
    simp [firstSimpleRootIndex, secondSimpleRootIndex] at hvalues
  have hsubset : {firstSimpleRootIndex n hthree, secondSimpleRootIndex n hthree} ⊆
      ideal.roots := by
    intro index hmem
    rcases Finset.mem_insert.mp hmem with hfirst | hsecond
    · simpa only [hfirst] using ideal.first_mem
    · rw [Finset.mem_singleton] at hsecond
      simpa only [hsecond] using ideal.second_mem
  simpa only [Finset.card_pair hdistinct] using Finset.card_le_card hsubset

/-- A Hessenberg ideal has at most as many roots as the whole positive root system. -/
theorem card_le {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree) :
    ideal.roots.card ≤ n := by
  simpa only [Fintype.card_fin] using ideal.roots.card_le_univ

/-- The full Hessenberg ideal contains all `n` positive roots. -/
@[simp] theorem card_full (n : ℕ) (hthree : 3 ≤ n) : (full n hthree).roots.card = n := by
  simp only [full, Finset.card_univ, Fintype.card_fin]

/-- An ideal has maximum cardinality exactly when it is the full root system. -/
theorem card_eq_iff_full {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree) :
    ideal.roots.card = n ↔ ideal = full n hthree := by
  constructor
  · intro hcard
    apply ext
    apply (Finset.card_eq_iff_eq_univ ideal.roots).mp
    simpa only [Fintype.card_fin] using hcard
  · rintro rfl
    exact card_full n hthree

end HessenbergSpace

end Schubert.DihedralSplines
