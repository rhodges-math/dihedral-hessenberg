import Schubert.Dihedral.RootBlock

/-! # Translation of alternating blocks -/

namespace Schubert.Dihedral

/-- Left translation changes only the base of an alternating block. -/
theorem alternatingBlock_translate {n : ℕ} (translate vertex : DihedralGroup n)
    (alpha beta : PositiveRoot n) (half : ℕ) :
    alternatingBlock (translate * vertex) alpha beta half =
      (alternatingBlock vertex alpha beta half).image (fun target => translate * target) := by
  classical
  simp only [alternatingBlock, Finset.image_image, Function.comp_def, mul_assoc]

/-- Translation preserves membership in the corresponding translated alternating block. -/
theorem mem_translated_block {n : ℕ} (translate vertex target : DihedralGroup n)
    (alpha beta : PositiveRoot n) (half : ℕ) :
    translate * target ∈ alternatingBlock (translate * vertex) alpha beta half ↔
      target ∈ alternatingBlock vertex alpha beta half := by
  classical
  rw [alternatingBlock_translate, Finset.mem_image]
  constructor
  · rintro ⟨current, hcurrent, heq⟩
    rwa [mul_left_cancel heq] at hcurrent
  · intro htarget
    exact ⟨target, htarget, rfl⟩

end Schubert.Dihedral
