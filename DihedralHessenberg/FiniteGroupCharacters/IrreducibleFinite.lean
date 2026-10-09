import TauCeti.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite-dimensionality of irreducible finite monoid actions -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- The finite orbit of any nonzero vector spans an irreducible finite monoid action. -/
theorem irreducible_finite {K G V : Type*} [Field K] [Monoid G] [Finite G]
    [AddCommGroup V] [Module K V] (action : Representation K G V)
    (hirreducible : action.IsIrreducible) : Module.Finite K V := by
  let : action.IsIrreducible := hirreducible
  let : Nontrivial V := Representation.IsIrreducible.nontrivial hirreducible
  obtain ⟨vector, hnonzero⟩ := exists_ne (0 : V)
  let orbitSpan := Submodule.span K (Set.range fun element => action element vector)
  let subrepresentation : Subrepresentation action :=
    { toSubmodule := orbitSpan
      apply_mem_toSubmodule := fun element {value} hvalue => by
        apply Submodule.span_induction (p := fun value _ => action element value ∈ orbitSpan)
          ?_ ?_ ?_ ?_ hvalue
        · rintro value ⟨byElement, rfl⟩
          apply Submodule.subset_span
          refine ⟨element * byElement, ?_⟩
          change action (element * byElement) vector = action element (action byElement vector)
          rw [map_mul]
          rfl
        · simpa only [map_zero] using orbitSpan.zero_mem
        · intro first second _ _ hfirst hsecond
          simpa only [map_add] using orbitSpan.add_mem hfirst hsecond
        · intro scalar value _ hvalue
          simpa only [map_smul] using orbitSpan.smul_mem scalar hvalue }
  have hcontains : vector ∈ subrepresentation.toSubmodule := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hnonbottom : subrepresentation ≠ ⊥ := by
    intro hequal
    rw [hequal] at hcontains
    exact hnonzero hcontains
  have htop := (eq_bot_or_eq_top subrepresentation).resolve_left hnonbottom
  have hspan : orbitSpan = ⊤ := congrArg Subrepresentation.toSubmodule htop
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range _)

end Schubert.FiniteGroupCharacters
