import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Equal finite dimensions in every comapped degree make a graded embedding surjective. -/

noncomputable section
namespace Schubert.Splines

/-- Equal finite dimensions in every comapped degree make a graded embedding surjective. -/
theorem surjective_of_piece_finrank {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (pieces : ℕ → Submodule K N) (hinternal : DirectSum.IsInternal pieces)
    (embedding : M →ₗ[K] N) (hinjective : Function.Injective embedding)
    (hfinite : ∀ degree, Module.Finite K ((pieces degree).comap embedding))
    (hfiniteTarget : ∀ degree, Module.Finite K (pieces degree))
    (hdimension : ∀ degree, Module.finrank K ((pieces degree).comap embedding) =
      Module.finrank K (pieces degree)) : Function.Surjective embedding := by
  have hcontained (degree : ℕ) : pieces degree ≤ embedding.range := by
    let := hfinite degree
    let := hfiniteTarget degree
    let restriction : (pieces degree).comap embedding →ₗ[K] pieces degree :=
      { toFun := fun value => ⟨embedding value.val, value.property⟩
        map_add' := fun first second => Subtype.ext (embedding.map_add first.val second.val)
        map_smul' := fun scalar value => Subtype.ext (embedding.map_smul scalar value.val) }
    have hinj : Function.Injective restriction := by
      intro first second heq
      exact Subtype.ext (hinjective (congrArg Subtype.val heq))
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdimension degree) (f := restriction)).mp hinj
    intro value hvalue
    obtain ⟨original, heq⟩ := hsurj ⟨value, hvalue⟩
    exact ⟨original.val, congrArg Subtype.val heq⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hinternal.submodule_iSup_eq_top]
  exact iSup_le hcontained

end Schubert.Splines
