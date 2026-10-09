import DihedralHessenberg.Dihedral.RootSeparator
import DihedralHessenberg.Dihedral.GeometricAscent
import DihedralHessenberg.Dihedral.RootSubsetImages
import DihedralHessenberg.Dihedral.RealLinearAction
import DihedralHessenberg.Dihedral.RootCard

/-! # Simple reflections permute the remaining positive unit roots -/

namespace Schubert.Dihedral

private theorem simple_positive (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2)
    (beta : PositiveRoot n) (hne : beta ≠ simpleRoot n hthree simple) :
    realAction n (simpleRoot n hthree simple).reflection beta.val ∈ positiveRoots n := by
  let : NeZero n := ⟨by omega⟩
  have hroot := realAction_mem n (simpleRoot n hthree simple).reflection beta.val
    (Or.inl beta.property)
  rcases hroot with hpositive | hnegative
  · exact hpositive
  · have hinv : beta.index ∈ rightInversions n hthree (simpleReflection n simple) := by
      rw [← simpleRoot_reflection n hthree simple]
      apply (mem_rightInversions_iff_negative_image n hthree _ beta.index).mpr
      change -realAction n (simpleRoot n hthree simple).reflection beta.val ∈
        positiveRoots n at hnegative
      change -realAction n (simpleRoot n hthree simple).reflection
        (positiveRoot n beta.index) ∈ positiveRoots n
      rw [beta.index_val]
      exact hnegative
    have hsingleton := rightInversions_simple_eq_singleton n hthree simple
      (simpleRoot n hthree simple).index (simpleRoot_reflection n hthree simple)
    rw [hsingleton, Finset.mem_singleton] at hinv
    exact (hne (PositiveRoot.index_injective n hinv)).elim

private theorem reflection_normal (n : ℕ) (alpha : PositiveRoot n) :
    realAction n alpha.reflection alpha.val = -alpha.val := by
  have h := alpha.scaled_reflection 1 one_ne_zero alpha.val
  have hunit := roots_unit alpha.val (Or.inl alpha.property)
  simp only [one_smul, hunit, div_one, mul_one] at h
  rw [← h]
  funext coordinate
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Each simple reflection bijects the other positive root vectors onto themselves. -/
theorem simple_except_bijOn (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2) :
    Set.BijOn (realAction n (simpleRoot n hthree simple).reflection)
      (positiveRoots n \ {(simpleRoot n hthree simple).val})
      (positiveRoots n \ {(simpleRoot n hthree simple).val}) := by
  let : NeZero n := ⟨by omega⟩
  let alpha := simpleRoot n hthree simple
  have involutive (vector : RealPlane) :
      realAction n alpha.reflection (realAction n alpha.reflection vector) = vector := by
    rw [← realAction_mul_plane, alpha.reflection_square, realAction_one]
    rfl
  have maps : Set.MapsTo (realAction n alpha.reflection)
      (positiveRoots n \ {alpha.val}) (positiveRoots n \ {alpha.val}) := by
    intro vector hvector
    have hne : (⟨vector, hvector.1⟩ : PositiveRoot n) ≠ alpha := by
      intro heq
      exact hvector.2 (congrArg Subtype.val heq)
    refine ⟨simple_positive n hthree simple ⟨vector, hvector.1⟩ hne, ?_⟩
    intro heq
    have hinverse := congrArg (realAction n alpha.reflection) heq
    rw [involutive, reflection_normal] at hinverse
    obtain ⟨index, hindex⟩ := hvector.1
    have hnegative : positiveRoot n index = -positiveRoot n alpha.index := by
      simpa only [hindex, PositiveRoot.index_val] using hinverse
    exact positiveRoot_ne_neg n index alpha.index hnegative
  refine ⟨maps, ?_, ?_⟩
  · intro first hfirst second hsecond heq
    have hinverse := congrArg (realAction n alpha.reflection) heq
    change realAction n alpha.reflection (realAction n alpha.reflection first) =
      realAction n alpha.reflection (realAction n alpha.reflection second) at hinverse
    simpa only [involutive] using hinverse
  · intro vector hvector
    exact ⟨realAction n alpha.reflection vector, maps hvector, involutive vector⟩

end Schubert.Dihedral
