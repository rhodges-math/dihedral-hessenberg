import DihedralHessenberg.Dihedral.RootObjects
import DihedralHessenberg.Dihedral.RootSigns

/-! # Complexification of real root carriers -/

noncomputable section

namespace Schubert.Dihedral

/-- Complexification identifies positive vectors with their complex image set. -/
def positiveComplexEquiv (n : ℕ) :
    PositiveRoot n ≃ {vector : ComplexPlane // vector ∈ complexify '' positiveRoots n} :=
  Equiv.ofBijective (fun alpha => ⟨complexify alpha.val, ⟨alpha.val, alpha.property, rfl⟩⟩) (by
    constructor
    · intro alpha beta heq
      exact Subtype.ext (complexify_injective (congrArg Subtype.val heq))
    · intro vector
      obtain ⟨alpha, halpha, heq⟩ := vector.property
      exact ⟨⟨alpha, halpha⟩, Subtype.ext heq⟩)

/-- Complexification identifies the full signed vector roots with their complex image set. -/
def rootComplexEquiv (n : ℕ) :
    Root n ≃ {vector : ComplexPlane // vector ∈ complexify '' roots n} :=
  Equiv.ofBijective (fun alpha => ⟨complexify alpha.val, ⟨alpha.val, alpha.property, rfl⟩⟩) (by
    constructor
    · intro alpha beta heq
      exact Subtype.ext (complexify_injective (congrArg Subtype.val heq))
    · intro vector
      obtain ⟨alpha, halpha, heq⟩ := vector.property
      exact ⟨⟨alpha, halpha⟩, Subtype.ext heq⟩)

/-- The positive-root complexification has the complex vector as its value. -/
@[simp] theorem positiveComplexEquiv_val {n : ℕ} (alpha : PositiveRoot n) :
    (positiveComplexEquiv n alpha).val = complexify alpha.val := rfl

/-- Signed-root action commutes with the complexification equivalence. -/
theorem rootComplexEquiv_action {n : ℕ} [NeZero n] (element : DihedralGroup n)
    (alpha : Root n) :
    (rootComplexEquiv n (Root.action element alpha)).val =
      vectorOperator n element (rootComplexEquiv n alpha).val :=
  realAction_complexify n element alpha.val alpha.property

end Schubert.Dihedral
