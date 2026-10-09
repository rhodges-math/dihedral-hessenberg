import DihedralHessenberg.Dihedral.Inversions

/-! # Reduced words and inversion sequences

A word is reduced exactly when its canonical left inversion sequence has no repetitions.
This criterion lets explicit reflection formulas establish reducedness without replacing
the canonical Coxeter length.
-/

namespace Schubert.Dihedral

/-- A word with pairwise distinct canonical left inversions is reduced. -/
theorem isReduced_of_nodup_leftInvSeq (n : ℕ) (hthree : 3 ≤ n)
    (word : List (Fin 2))
    (hnodup : ((coxeterSystem n hthree).leftInvSeq word).Nodup) :
    IsReduced n hthree word := by
  let cs := coxeterSystem n hthree
  change (cs.leftInvSeq word).Nodup at hnodup
  change cs.IsReduced word
  induction word with
  | nil => simp only [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_nil,
      CoxeterSystem.length_one, List.length_nil]
  | cons generator word ih =>
    rw [CoxeterSystem.leftInvSeq, List.nodup_cons] at hnodup
    have hword := ih (hnodup.2.of_map (MulAut.conj (cs.simple generator)))
    have hnot : ¬cs.IsLeftDescent (cs.wordProd word) generator := by
      intro hdescent
      have hmem : cs.simple generator ∈ cs.leftInvSeq word :=
        (cs.mem_leftInvSeq_iff_isLeftInversion hword).mpr
          ((cs.isLeftInversion_simple_iff_isLeftDescent _ _).mpr hdescent)
      apply hnodup.1
      apply List.mem_map.mpr
      refine ⟨cs.simple generator, hmem, ?_⟩
      simp only [MulAut.conj_apply, mul_inv_cancel_right]
    change cs.length (cs.wordProd (generator :: word)) = (generator :: word).length
    rw [CoxeterSystem.wordProd_cons, cs.not_isLeftDescent_iff.mp hnot, hword.eq]
    rfl

/-- Reducedness is equivalent to distinctness of the canonical left inversion sequence. -/
theorem isReduced_iff_nodup_leftInvSeq (n : ℕ) (hthree : 3 ≤ n)
    (word : List (Fin 2)) :
    IsReduced n hthree word ↔ ((coxeterSystem n hthree).leftInvSeq word).Nodup :=
  ⟨fun hword => hword.nodup_leftInvSeq, isReduced_of_nodup_leftInvSeq n hthree word⟩

end Schubert.Dihedral
