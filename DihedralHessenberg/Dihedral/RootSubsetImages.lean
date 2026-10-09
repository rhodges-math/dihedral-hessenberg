import DihedralHessenberg.Dihedral.RootSubsetCard

/-! # Signed-image bijections for arbitrary positive-root subsets -/

namespace Schubert.Dihedral

/-- Negation commutes with the real coordinate action. -/
theorem realAction_neg (n : ℕ) (element : DihedralGroup n) (alpha : RealPlane) :
    realAction n element (-alpha) = -realAction n element alpha := by
  have hneg : complexify (-alpha) = -complexify alpha := by
    funext coordinate
    simp only [complexify, Pi.neg_apply, Complex.ofReal_neg]
  funext coordinate
  change (vectorOperator n element (complexify (-alpha)) coordinate).re = _
  rw [hneg, map_neg]
  rfl

/-- An element acts injectively on the signed root set. -/
theorem realAction_injOn_roots (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    Set.InjOn (realAction n element) (roots n) := by
  intro alpha halpha beta hbeta heq
  have hinverse := congrArg (realAction n element⁻¹) heq
  rw [← realAction_mul n element⁻¹ element alpha halpha,
    ← realAction_mul n element⁻¹ element beta hbeta, inv_mul_cancel,
    realAction_one] at hinverse
  exact hinverse

namespace RootSubset

/-- Negative action images identify selected inversions with positive images of negative roots. -/
theorem negative_image_bijOn {n : ℕ} [NeZero n] (selected : RootSubset n)
    (element : DihedralGroup n) :
    Set.BijOn (fun alpha => -realAction n element alpha) (selected.inversions element)
      ((fun alpha => -realAction n element alpha) '' selected.carrier ∩ positiveRoots n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro alpha halpha
    exact ⟨⟨alpha, halpha.1, rfl⟩, halpha.2.2⟩
  · intro alpha halpha beta hbeta heq
    exact realAction_injOn_roots n element (Or.inl (selected.positive halpha.1))
      (Or.inl (selected.positive hbeta.1)) (neg_injective heq)
  · intro beta hbeta
    obtain ⟨⟨alpha, halpha, heq⟩, hpositive⟩ := hbeta
    change -realAction n element alpha = beta at heq
    exact ⟨alpha, (selected.mem_inversions element alpha).mpr
      ⟨halpha, heq.symm ▸ hpositive⟩, heq⟩

/-- Negative images are the images of the negative selected-root subset. -/
theorem image_negative {n : ℕ} (selected : RootSubset n) (element : DihedralGroup n) :
    (fun alpha => -realAction n element alpha) '' selected.carrier =
      realAction n element '' (Neg.neg '' selected.carrier) := by
  ext beta
  constructor
  · rintro ⟨alpha, halpha, rfl⟩
    exact ⟨-alpha, ⟨alpha, halpha, rfl⟩, realAction_neg n element alpha⟩
  · rintro ⟨_, ⟨alpha, halpha, rfl⟩, heq⟩
    exact ⟨alpha, halpha, (realAction_neg n element alpha).symm.trans heq⟩

/-- The inversion set is bijective with the positive vectors in w(-H). -/
theorem inversions_bijOn {n : ℕ} [NeZero n] (selected : RootSubset n)
    (element : DihedralGroup n) :
    Set.BijOn (fun alpha => -realAction n element alpha) (selected.inversions element)
      (realAction n element '' (Neg.neg '' selected.carrier) ∩ positiveRoots n) := by
  rw [← selected.image_negative element]
  exact selected.negative_image_bijOn element

end RootSubset

end Schubert.Dihedral
