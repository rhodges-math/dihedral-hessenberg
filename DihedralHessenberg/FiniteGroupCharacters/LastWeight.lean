import DihedralHessenberg.FiniteGroupCharacters.WeightMultiplicity

/-! # Splitting the final positive weight from a truncated sum -/

namespace Schubert.FiniteGroupCharacters

open scoped BigOperators

/-- The last positive degree has multiplicity one and all earlier positive degrees have two. -/
theorem positive_weight_sum {A : Type*} [AddCommMonoid A] (function : ℕ → A)
    (height : ℕ) (hheight : 1 ≤ height) :
    (∑ index : Fin height,
      (if height - (index.val + 1) = 0 then 1 else 2) • function (index.val + 1)) =
      function height + 2 • ∑ degree ∈ Finset.Ico 1 height, function degree := by
  obtain ⟨size, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : height ≠ 0)
  rw [Fin.sum_univ_castSucc]
  have hcoeff (index : Fin size) : size + 1 - (index.val + 1) ≠ 0 := by
    have := index.isLt
    omega
  simp only [Fin.val_castSucc, Fin.val_last, Nat.succ_eq_add_one, Nat.sub_self,
    ite_true, one_nsmul, hcoeff, ite_false]
  rw [← Finset.smul_sum, Fin.sum_univ_eq_sum_range (fun index => function (index + 1)) _,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  exact add_comm _ _

end Schubert.FiniteGroupCharacters
