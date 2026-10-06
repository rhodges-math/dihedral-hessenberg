import Schubert.Dihedral.RankTwoRootVectors
import Schubert.Dihedral.RootSubsetImages

/-! # Bijections of left inversions at simple ascents -/

namespace Schubert.Dihedral.PositiveRoot

/-- A simple ascent bijects old left inversions onto the new inversions minus its simple vector. -/
theorem left_ascent_bijOn {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    Set.BijOn (realAction n alpha.reflection) (leftInversionSet n element)
      (leftInversionSet n (alpha.reflection * element) \ {alpha.val}) := by
  let : NeZero n := ⟨by omega⟩
  have hset := alpha.left_ascent hthree hsimple element hascent
  have hdisjoint := alpha.left_ascent_disjoint hthree hsimple element hascent
  refine ⟨?_, ?_, ?_⟩
  · intro beta hbeta
    have himage : realAction n alpha.reflection beta ∈
        realAction n alpha.reflection '' leftInversionSet n element := ⟨beta, hbeta, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hset]
      exact Or.inr himage
    · intro heq
      exact hdisjoint (heq ▸ himage)
  · intro beta hbeta gamma hgamma heq
    exact realAction_injOn_roots n alpha.reflection (Or.inl hbeta.1) (Or.inl hgamma.1) heq
  · intro beta hbeta
    rw [hset] at hbeta
    rcases hbeta.1 with heq | himage
    · exact (hbeta.2 heq).elim
    · exact himage

/-- Positive-root inversion subtypes are equivalent with the specified geometric image. -/
theorem left_ascent_equiv {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    ∃ equivalence : {beta : PositiveRoot n // beta.val ∈ leftInversionSet n element} ≃
        {beta : PositiveRoot n //
          beta.val ∈ leftInversionSet n (alpha.reflection * element) ∧ beta ≠ alpha},
      ∀ beta, (equivalence beta).val.val = realAction n alpha.reflection beta.val.val := by
  classical
  have hbij := alpha.left_ascent_bijOn hthree hsimple element hascent
  let function : {beta : PositiveRoot n // beta.val ∈ leftInversionSet n element} →
      {beta : PositiveRoot n //
        beta.val ∈ leftInversionSet n (alpha.reflection * element) ∧ beta ≠ alpha} := fun beta =>
    ⟨⟨realAction n alpha.reflection beta.val.val, (hbij.mapsTo beta.property).1.1⟩,
      (hbij.mapsTo beta.property).1, by
        intro heq
        exact (hbij.mapsTo beta.property).2 (congrArg Subtype.val heq)⟩
  have hinjective : Function.Injective function := by
    intro beta gamma heq
    apply Subtype.ext
    apply Subtype.ext
    exact hbij.injOn beta.property gamma.property
      (congrArg (fun value => value.val.val) heq)
  have hsurjective : Function.Surjective function := by
    intro gamma
    have htarget : gamma.val.val ∈
        leftInversionSet n (alpha.reflection * element) \ {alpha.val} :=
      ⟨gamma.property.1, fun heq => gamma.property.2 (Subtype.ext heq)⟩
    obtain ⟨beta, hbeta, himage⟩ := hbij.surjOn htarget
    refine ⟨⟨⟨beta, hbeta.1⟩, hbeta⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext himage
  exact ⟨Equiv.ofBijective function ⟨hinjective, hsurjective⟩, fun _ => rfl⟩

end Schubert.Dihedral.PositiveRoot
