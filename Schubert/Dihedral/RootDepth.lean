import Schubert.Dihedral.RootRescaling
import Schubert.Dihedral.RootInversionSets
import Schubert.Dihedral.InversionBounds

/-! # Root depth from the signed dihedral action -/

noncomputable section

namespace Schubert.Dihedral.PositiveRoot

private theorem negative_witness {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    ∃ size : ℕ, ∃ element : DihedralGroup n,
      length n hthree element = size ∧ -realAction n element alpha.val ∈ positiveRoots n := by
  refine ⟨length n hthree alpha.reflection, alpha.reflection, rfl, ?_⟩
  have h := alpha.scaled_reflection 1 one_ne_zero alpha.val
  have hunit := roots_unit alpha.val (Or.inl alpha.property)
  simp only [one_smul, hunit, div_one, mul_one] at h
  have heq : realAction n alpha.reflection alpha.val = -alpha.val := by
    rw [← h]
    funext coordinate
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  simpa only [heq, neg_neg] using alpha.property

/-- The least simple-generator length sending a positive vector to a negative root. -/
def depth {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) : ℕ :=
  by
    classical
    exact Nat.find (negative_witness hthree alpha)

/-- A group element of the root depth attains negativity. -/
theorem depth_spec {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    ∃ element : DihedralGroup n, length n hthree element = alpha.depth hthree ∧
      -realAction n element alpha.val ∈ positiveRoots n :=
  by
    classical
    exact Nat.find_spec (negative_witness hthree alpha)

/-- Every element sending the root negative has length at least its root depth. -/
theorem depth_le {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (element : DihedralGroup n)
    (hnegative : -realAction n element alpha.val ∈ positiveRoots n) :
    alpha.depth hthree ≤ length n hthree element :=
  by
    classical
    exact Nat.find_min' (negative_witness hthree alpha) ⟨element, rfl, hnegative⟩

/-- Alternating layers give a lower bound for root depth. -/
theorem layer_le_depth {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    alpha.index.val / 2 + 1 ≤ alpha.depth hthree := by
  obtain ⟨element, hlength, hnegative⟩ := alpha.depth_spec hthree
  have hinversion : alpha.index ∈ rightInversions n hthree element := by
    apply (mem_rightInversionSet n hthree element alpha.index).mp
    exact ⟨by simpa only [alpha.index_val] using alpha.property,
      by simpa only [alpha.index_val] using hnegative⟩
  have hbound := IndexedRoots.length_bound_at_inversion n hthree element alpha.index hinversion
  rw [length_rootReflection, hlength] at hbound
  omega

end Schubert.Dihedral.PositiveRoot
