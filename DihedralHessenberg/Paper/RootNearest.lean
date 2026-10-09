import DihedralHessenberg.Dihedral.RootHalfspace
import DihedralHessenberg.Paper.RootOrder

/-! # The closest positive roots to the separating hyperplane -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private theorem simple_pairing_eq (n : ℕ) (hthree : 3 ≤ n) :
    realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) =
      realBilinearForm (simpleRoot n hthree 1).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) := by
  have hfirst := roots_unit (simpleRoot n hthree 0).val
    (Or.inl (simpleRoot n hthree 0).property)
  have hsecond := roots_unit (simpleRoot n hthree 1).val
    (Or.inl (simpleRoot n hthree 1).property)
  simp only [realBilinearForm, Pi.add_apply] at hfirst hsecond ⊢
  nlinarith

private theorem simple_le_or_second (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    RootOrder n hthree (simpleRoot n hthree 0) alpha ∨ alpha = simpleRoot n hthree 1 := by
  by_cases hone : alpha.index.val = 1
  · right
    apply (positiveRootEquiv n).symm.injective
    change alpha.index = (positiveRootEquiv n).symm (simpleRoot n hthree 1)
    rw [simpleRoot_one, Equiv.symm_apply_apply]
    apply Fin.ext
    exact hone
  · left
    rw [rootOrder_indices, simpleRoot_zero, PositiveRoot.index_equiv,
      rootLE_iff_eq_or_layer_lt]
    by_cases hzero : alpha.index.val = 0
    · left
      apply Fin.ext
      exact hzero.symm
    · right
      change 0 / 2 < alpha.index.val / 2
      omega

/-- Every nonsimple positive root has strictly larger projection than the two simple roots. -/
theorem nonsimple_pairing_gt (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hfirst : alpha ≠ simpleRoot n hthree 0) (hsecond : alpha ≠ simpleRoot n hthree 1) :
    realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) <
      realBilinearForm alpha.val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) := by
  have horder := (simple_le_or_second n hthree alpha).resolve_right hsecond
  obtain ⟨a, b, ha, hb, hexpansion⟩ := horder
  have hsum : 0 < a + b := by
    by_contra hnot
    have hzeroa : a = 0 := by linarith
    have hzerob : b = 0 := by linarith
    rw [hzeroa, hzerob, zero_smul, zero_smul, add_zero, sub_eq_zero] at hexpansion
    exact hfirst (Subtype.ext hexpansion)
  have hdistrib (first second : RealPlane) :
      realBilinearForm (a • first + b • second) (first + second) =
        a * realBilinearForm first (first + second) +
          b * realBilinearForm second (first + second) := by
    simp only [realBilinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdiff : realBilinearForm alpha.val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) -
      realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) =
      (a + b) * realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) := by
    have hsub : realBilinearForm (alpha.val - (simpleRoot n hthree 0).val)
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) =
      realBilinearForm alpha.val
          ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) -
        realBilinearForm (simpleRoot n hthree 0).val
          ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) := by
      simp only [realBilinearForm, Pi.sub_apply]
      ring
    rw [← hsub, hexpansion, hdistrib, ← simple_pairing_eq n hthree]
    ring
  have hpositive := (simpleRoot n hthree 0).halfspace_pos hthree
  have hgt := mul_pos hsum hpositive
  rw [← hdiff] at hgt
  linarith

/-- Exactly the simple pair minimizes positive projection onto the separating normal. -/
theorem simple_pairing_minimum (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    realBilinearForm alpha.val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) ≤
      realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) ↔
      alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1 := by
  constructor
  · intro hle
    by_contra hnot
    have hfirst : alpha ≠ simpleRoot n hthree 0 := fun heq => hnot (Or.inl heq)
    have hsecond : alpha ≠ simpleRoot n hthree 1 := fun heq => hnot (Or.inr heq)
    exact (not_lt_of_ge hle) (nonsimple_pairing_gt n hthree alpha hfirst hsecond)
  · rintro (rfl | rfl)
    · exact le_rfl
    · exact le_of_eq (simple_pairing_eq n hthree).symm


/-- The simple-root projection is a lower bound for every positive-root projection. -/
theorem simple_pairing_le (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) ≤
      realBilinearForm alpha.val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) := by
  by_cases hfirst : alpha = simpleRoot n hthree 0
  · rw [hfirst]
  by_cases hsecond : alpha = simpleRoot n hthree 1
  · exact le_of_eq (hsecond ▸ simple_pairing_eq n hthree)
  exact le_of_lt (nonsimple_pairing_gt n hthree alpha hfirst hsecond)

end Schubert.DihedralSplines
