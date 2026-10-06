import Schubert.Dihedral.RootSum
import Schubert.Dihedral.ConeInterior

/-! # Generic positive chambers are images of the canonical positive roots -/

namespace Schubert.Dihedral.Separator

/-- A generic separator admits a group translate with both simple vectors on its positive side. -/
theorem exists_positive_pair {n : ℕ} (data : Separator n) (hthree : 3 ≤ n) :
    ∃ element : DihedralGroup n, ∀ simple : Fin 2,
      0 < realBilinearForm (realAction n element (simpleRoot n hthree simple).val) data.normal := by
  classical
  let : NeZero n := ⟨by omega⟩
  let height : DihedralGroup n → ℝ := fun element =>
    realBilinearForm (realAction n element (rootSum n)) data.normal
  obtain ⟨element, _, hmax⟩ := Finset.exists_max_image Finset.univ height
    (Finset.univ_nonempty)
  refine ⟨element, ?_⟩
  intro simple
  let alpha := simpleRoot n hthree simple
  have hbound := hmax (element * alpha.reflection) (Finset.mem_univ _)
  have hflip : height (element * alpha.reflection) = height element -
      2 * realBilinearForm (realAction n element alpha.val) data.normal := by
    dsimp [height]
    rw [realAction_mul_plane, rootSum_reflection]
    change realBilinearForm ((realLinearEquiv n element) (rootSum n - 2 • alpha.val))
      data.normal = _
    rw [map_sub, map_nsmul]
    change realBilinearForm (realAction n element (rootSum n) -
      2 • realAction n element alpha.val) data.normal = _
    simp only [realBilinearForm, Pi.sub_apply, Pi.smul_apply]
    ring
  have hnonzero := data.generic (realAction n element alpha.val)
    (realAction_mem n element alpha.val (Or.inl alpha.property))
  rw [hflip] at hbound
  have hnonneg : 0 ≤ realBilinearForm (realAction n element alpha.val) data.normal := by
    linarith
  exact lt_of_le_of_ne hnonneg (Ne.symm hnonzero)

/-- Every generic positive side is a translate of the canonical positive-root set. -/
theorem exists_chamber {n : ℕ} (data : Separator n) (hthree : 3 ≤ n) :
    ∃ element : DihedralGroup n,
      data.positive = realAction n element '' positiveRoots n := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨element, hsimple⟩ := data.exists_positive_pair hthree
  have hpositive (alpha : PositiveRoot n) :
      0 < realBilinearForm (realAction n element alpha.val) data.normal := by
    by_cases hfirst : alpha = simpleRoot n hthree 0
    · subst alpha
      exact hsimple 0
    by_cases hsecond : alpha = simpleRoot n hthree 1
    · subst alpha
      exact hsimple 1
    let a := rootConeCoordinates n alpha.index 0
    let b := rootConeCoordinates n alpha.index 1
    have ha : 1 ≤ a := coneCoordinates_interior n hthree alpha hfirst hsecond 0
    have hb : 1 ≤ b := coneCoordinates_interior n hthree alpha hfirst hsecond 1
    have hexpansion : alpha.val =
        a • (simpleRoot n hthree 0).val + b • (simpleRoot n hthree 1).val := by
      rw [simpleRoot_zero, simpleRoot_one, positiveRootEquiv_val, positiveRootEquiv_val,
        ← positiveRoot_eq_rootConeCoordinates n hthree alpha.index, PositiveRoot.index_val]
    have hlinear : realAction n element alpha.val =
        a • realAction n element (simpleRoot n hthree 0).val +
          b • realAction n element (simpleRoot n hthree 1).val := by
      change (realLinearEquiv n element) alpha.val = _
      rw [hexpansion, map_add, map_smul, map_smul]
      rfl
    have hpairing : realBilinearForm (realAction n element alpha.val) data.normal =
        a * realBilinearForm (realAction n element (simpleRoot n hthree 0).val) data.normal +
          b * realBilinearForm (realAction n element (simpleRoot n hthree 1).val) data.normal := by
      rw [hlinear]
      simp only [realBilinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpairing]
    exact add_pos (mul_pos (by linarith) (hsimple 0))
      (mul_pos (by linarith) (hsimple 1))
  refine ⟨element, ?_⟩
  ext vector
  constructor
  · intro hvector
    have hinverse : realAction n element (realAction n element⁻¹ vector) = vector := by
      rw [← realAction_mul_plane, mul_inv_cancel, realAction_one]
      rfl
    have hroot := realAction_mem n element⁻¹ vector hvector.1
    rcases hroot with hpos | hneg
    · exact ⟨realAction n element⁻¹ vector, hpos, hinverse⟩
    · have hdot := hpositive ⟨-realAction n element⁻¹ vector, hneg⟩
      rw [realAction_neg, hinverse] at hdot
      have hvdot := hvector.2
      simp only [realBilinearForm, Pi.neg_apply, neg_mul] at hdot hvdot
      linarith
  · rintro ⟨root, hroot, rfl⟩
    exact ⟨realAction_mem n element root (Or.inl hroot), hpositive ⟨root, hroot⟩⟩

end Schubert.Dihedral.Separator
