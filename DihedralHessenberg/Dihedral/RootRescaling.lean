import DihedralHessenberg.Dihedral.RootAxioms
import DihedralHessenberg.Dihedral.FaithfulRealization
import DihedralHessenberg.Dihedral.RootObjectAction
import DihedralHessenberg.Dihedral.UnitDirections
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic

/-! # Positive radial rescalings preserve root directions and reflections -/

namespace Schubert.Dihedral.PositiveRoot

variable {n : ℕ}

private theorem pairing_scale (scalar : ℝ) (vector : RealPlane) :
    realBilinearForm (scalar • vector) (scalar • vector) =
      scalar ^ 2 * realBilinearForm vector vector := by
  simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul]
  ring

/-- A positive radial rescaling of the positive unit vectors is injective. -/
theorem scaled_injective (radius : PositiveRoot n → ℝ)
    (hpositive : ∀ alpha, 0 < radius alpha) :
    Function.Injective (fun alpha : PositiveRoot n => radius alpha • alpha.val) := by
  intro alpha beta heq
  change radius alpha • alpha.val = radius beta • beta.val at heq
  have ha : realBilinearForm alpha.val alpha.val = 1 := by
    rw [← alpha.index_val]
    exact positiveRoot_unit n alpha.index
  have hb : realBilinearForm beta.val beta.val = 1 := by
    rw [← beta.index_val]
    exact positiveRoot_unit n beta.index
  have hsquare := congrArg (fun vector => realBilinearForm vector vector) heq
  rw [pairing_scale, pairing_scale, ha, hb, mul_one, mul_one] at hsquare
  have hradius : radius alpha = radius beta := by
    nlinarith [hpositive alpha, hpositive beta]
  apply Subtype.ext
  rw [hradius] at heq
  exact (smul_right_injective RealPlane (ne_of_gt (hpositive beta))) heq

/-- Rescaling a root by a nonzero real scalar leaves its normal reflection unchanged. -/
theorem scaled_reflection (alpha : PositiveRoot n) (scalar : ℝ) (hscalar : scalar ≠ 0)
    (vector : RealPlane) :
    vector - (2 * realBilinearForm vector (scalar • alpha.val) /
      realBilinearForm (scalar • alpha.val) (scalar • alpha.val)) •
      (scalar • alpha.val) = realAction n alpha.reflection vector := by
  have hunit : realBilinearForm alpha.val alpha.val = 1 := by
    rw [← alpha.index_val]
    exact positiveRoot_unit n alpha.index
  have hright : realBilinearForm vector (scalar • alpha.val) =
      scalar * realBilinearForm vector alpha.val := by
    simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul]
    ring
  rw [pairing_scale, hunit, mul_one, hright, alpha.realAction_reflection, smul_smul]
  congr 2
  field_simp

/-- A conjugacy-invariant positive root radius gives a reflection-closed signed vector set. -/
theorem scaled_reflection_closed [NeZero n] (radius : PositiveRoot n → ℝ)
    (hpositive : ∀ alpha, 0 < radius alpha)
    (hclass : ∀ alpha beta, IsConj alpha.reflection beta.reflection → radius alpha = radius beta)
    (alpha beta : PositiveRoot n) :
    let image := radius beta • beta.val -
      (2 * realBilinearForm (radius beta • beta.val) (radius alpha • alpha.val) /
        realBilinearForm (radius alpha • alpha.val) (radius alpha • alpha.val)) •
        (radius alpha • alpha.val)
    image ∈ Set.range (fun gamma : PositiveRoot n => radius gamma • gamma.val) ∨
      -image ∈ Set.range (fun gamma : PositiveRoot n => radius gamma • gamma.val) := by
  dsimp only
  rw [scaled_reflection alpha (radius alpha) (ne_of_gt (hpositive alpha)),
    realAction_smul_plane]
  have hroot := realAction_mem n alpha.reflection beta.val (Or.inl beta.property)
  change (∃ index, positiveRoot n index = realAction n alpha.reflection beta.val) ∨
    (∃ index, positiveRoot n index = -realAction n alpha.reflection beta.val) at hroot
  rcases hroot with ⟨index, hindex⟩ | ⟨index, hindex⟩
  · let gamma := positiveRootEquiv n index
    have himage : realAction n alpha.reflection beta.val = gamma.val := hindex.symm
    have hreflection := signed_conjugation alpha.reflection beta gamma (Or.inl himage)
    have hradius := hclass beta gamma (isConj_iff.mpr ⟨alpha.reflection, hreflection.symm⟩)
    left
    rw [himage, hradius]
    exact ⟨gamma, rfl⟩
  · let gamma := positiveRootEquiv n index
    have himage : realAction n alpha.reflection beta.val = -gamma.val := by
      change _ = -positiveRoot n index
      rw [hindex, neg_neg]
    have hreflection := signed_conjugation alpha.reflection beta gamma (Or.inr himage)
    have hradius := hclass beta gamma (isConj_iff.mpr ⟨alpha.reflection, hreflection.symm⟩)
    right
    rw [himage, hradius, smul_neg, neg_neg]
    exact ⟨gamma, rfl⟩

end Schubert.Dihedral.PositiveRoot
