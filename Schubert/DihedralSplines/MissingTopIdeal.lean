import Schubert.DihedralSplines.HessenbergVectorClassification
import Schubert.DihedralSplines.DominanceOdd

/-! # The Hessenberg ideal omitting the final positive root -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- All positive vectors except the final numbered root. -/
def withoutLast (n : ℕ) (hthree : 3 ≤ n) : HessenbergIdeal n hthree :=
  Classical.choose (exists_initial n hthree (n - 1) (by omega) (by omega))

private theorem initial (n : ℕ) (hthree : 3 ≤ n) :
    (withoutLast n hthree).carrier.ncard = n - 1 ∧
      (withoutLast n hthree).carrier =
        positiveRoot n '' {index : Fin n | index.val < n - 1} :=
  Classical.choose_spec (exists_initial n hthree (n - 1) (by omega) (by omega))

/-- Removing the final positive root leaves exactly n−1 vectors. -/
theorem withoutLast_card (n : ℕ) (hthree : 3 ≤ n) :
    (withoutLast n hthree).carrier.ncard = n - 1 := (initial n hthree).1

/-- Numbered membership is precisely membership below the final index. -/
theorem withoutLast_mem (n : ℕ) (hthree : 3 ≤ n) (index : Fin n) :
    (positiveRootEquiv n index).val ∈ withoutLast n hthree ↔ index.val < n - 1 := by
  change positiveRoot n index ∈ (withoutLast n hthree).carrier ↔ _
  rw [(initial n hthree).2]
  simp only [Set.mem_image, Set.mem_ofPred_eq, (positiveRoot_injective n).eq_iff,
    exists_eq_right]

/-- The carrier is the positive root set with its final vector removed. -/
theorem withoutLast_carrier (n : ℕ) (hthree : 3 ≤ n) :
    (withoutLast n hthree).carrier =
      positiveRoots n \ {positiveRoot n ⟨n - 1, by omega⟩} := by
  rw [(initial n hthree).2]
  ext vector
  constructor
  · rintro ⟨index, hindex, rfl⟩
    change index.val < n - 1 at hindex
    refine ⟨⟨index, rfl⟩, ?_⟩
    intro heq
    have hindices := positiveRoot_injective n heq
    have hval := congrArg Fin.val hindices
    change index.val = n - 1 at hval
    omega
  · rintro ⟨⟨index, rfl⟩, hne⟩
    refine ⟨index, ?_, rfl⟩
    have hi := index.isLt
    by_contra hnot
    change ¬index.val < n - 1 at hnot
    have hval : index.val = n - 1 := by omega
    have hindex : index = ⟨n - 1, by omega⟩ := Fin.ext hval
    exact hne (congrArg (positiveRoot n) hindex)

/-- The ideal omitting the final vector is always proper. -/
theorem withoutLast_proper (n : ℕ) (hthree : 3 ≤ n) :
    (withoutLast n hthree).carrier ≠ positiveRoots n := by
  intro heq
  have hmem : (positiveRootEquiv n ⟨n - 1, by omega⟩).val ∈ withoutLast n hthree := by
    change positiveRoot n ⟨n - 1, by omega⟩ ∈ (withoutLast n hthree).carrier
    rw [heq]
    exact ⟨_, rfl⟩
  rw [withoutLast_mem] at hmem
  change n - 1 < n - 1 at hmem
  exact (lt_irrefl _ hmem).elim

/-- For even n, the omitted-root ideal has the indicated odd middle size. -/
theorem withoutLast_even (n : ℕ) (hthree : 3 ≤ n) (heven : Even n) :
    (withoutLast n hthree).carrier.ncard = 2 * (n / 2 - 1) + 1 := by
  have hmod := (Nat.even_iff).mp heven
  rw [withoutLast_card]
  omega

/-- For odd n, the omitted-root ideal has the indicated even middle size. -/
theorem withoutLast_odd (n : ℕ) (hthree : 3 ≤ n) (hodd : Odd n) :
    (withoutLast n hthree).carrier.ncard = 2 * ((n - 1) / 2) := by
  have hmod := (Nat.odd_iff).mp hodd
  rw [withoutLast_card]
  omega

/-- For even n, the first simple root is dominant exactly when n/2 is odd. -/
theorem withoutLast_first (n : ℕ) (hthree : 3 ≤ n) (heven : Even n) :
    (withoutLast n hthree).IsDominant (simpleRoot n hthree 0) ↔ ¬Even (n / 2) := by
  have hmod := (Nat.even_iff).mp heven
  have hcard : (withoutLast n hthree).carrier.ncard = 2 * (n / 2 - 1) + 1 := by
    rw [withoutLast_card]
    omega
  have hlast : 2 * (n / 2 - 1) + 1 = n - 1 :=
    hcard.symm.trans (withoutLast_card n hthree)
  have hprev : 2 * (n / 2 - 1) < n - 1 := by omega
  rw [dominant_first_iff (withoutLast n hthree) (n / 2 - 1) hcard
    (withoutLast_proper n hthree)]
  have hhalf : n - (n / 2 - 1) - 1 = n / 2 := by omega
  rw [hhalf]
  split_ifs with hhalfEven
  · rw [withoutLast_mem]
    simp only [hhalfEven, not_true_eq_false]
    change 2 * (n / 2 - 1) + 1 < n - 1 ↔ False
    rw [hlast]
    exact iff_false_intro (lt_irrefl _)
  · rw [withoutLast_mem]
    simp only [hhalfEven, not_false_eq_true]
    change 2 * (n / 2 - 1) < n - 1 ↔ True
    exact iff_true_intro hprev

/-- For even n, the second simple root is dominant exactly when n/2 is even. -/
theorem withoutLast_second (n : ℕ) (hthree : 3 ≤ n) (heven : Even n) :
    (withoutLast n hthree).IsDominant (simpleRoot n hthree 1) ↔ Even (n / 2) := by
  have hmod := (Nat.even_iff).mp heven
  have hcard : (withoutLast n hthree).carrier.ncard = 2 * (n / 2 - 1) + 1 := by
    rw [withoutLast_card]
    omega
  have hlast : 2 * (n / 2 - 1) + 1 = n - 1 :=
    hcard.symm.trans (withoutLast_card n hthree)
  have hprev : 2 * (n / 2 - 1) < n - 1 := by omega
  rw [dominant_second_iff (withoutLast n hthree) (n / 2 - 1) hcard
    (withoutLast_proper n hthree)]
  have hhalf : n - (n / 2 - 1) - 1 = n / 2 := by omega
  rw [hhalf]
  split_ifs with hhalfEven
  · rw [withoutLast_mem]
    simp only [hhalfEven]
    change 2 * (n / 2 - 1) < n - 1 ↔ True
    exact iff_true_intro hprev
  · rw [withoutLast_mem]
    simp only [hhalfEven]
    change 2 * (n / 2 - 1) + 1 < n - 1 ↔ False
    rw [hlast]
    exact iff_false_intro (lt_irrefl _)

end Schubert.DihedralSplines.HessenbergIdeal
