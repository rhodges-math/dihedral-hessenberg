import Schubert.FiniteGroupCharacters.GradedSection

/-! # Graded equivariant sections of homogeneous quotient maps -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- A surjective homogeneous quotient action has a graded equivariant section. -/
theorem graded_quotient_section {K G V W : Type*} [Field K] [Group G] [Finite G]
    [NeZero (Nat.card G : K)] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    {source : Representation K G V} {target : Representation K G W}
    (sourcePieces : ℕ → Subrepresentation source)
    (targetPieces : ℕ → Subrepresentation target)
    [DirectSum.Decomposition (fun degree => (targetPieces degree).toSubmodule)]
    (projection : source.IntertwiningMap target)
    (hpiece : ∀ degree (value : (sourcePieces degree).toSubmodule),
      projection value.val ∈ (targetPieces degree).toSubmodule)
    (hsurjective : ∀ degree (value : (targetPieces degree).toSubmodule),
      ∃ original : (sourcePieces degree).toSubmodule, projection original.val = value.val) :
    ∃ lift : target.IntertwiningMap source,
      (∀ value, projection (lift value) = value) ∧
      ∀ degree (value : (targetPieces degree).toSubmodule),
        lift value.val ∈ (sourcePieces degree).toSubmodule := by
  let pieceMap (degree : ℕ) :
      (sourcePieces degree).toRepresentation.IntertwiningMap
        (targetPieces degree).toRepresentation :=
    { toLinearMap :=
        { toFun := fun value => ⟨projection value.val, hpiece degree value⟩
          map_add' := fun first second => Subtype.ext (map_add _ first.val second.val)
          map_smul' := fun scalar value => Subtype.ext (map_smul _ scalar value.val) }
      isIntertwining' element := by
        apply LinearMap.ext
        intro value
        apply Subtype.ext
        exact projection.isIntertwining source target element value.val }
  have hlifts (degree : ℕ) : ∃ lift :
      (targetPieces degree).toRepresentation.IntertwiningMap
        (sourcePieces degree).toRepresentation,
      ∀ value, pieceMap degree (lift value) = value := by
    apply equivariant_section (source := (sourcePieces degree).toRepresentation)
      (target := (targetPieces degree).toRepresentation) (pieceMap degree)
    intro value
    obtain ⟨original, horiginal⟩ := hsurjective degree value
    exact ⟨original, Subtype.ext horiginal⟩
  let lifts degree := Classical.choose (hlifts degree)
  let lift : target.IntertwiningMap source :=
    { toLinearMap := gradedLift sourcePieces targetPieces lifts
      isIntertwining' element := by
        apply LinearMap.ext
        intro value
        exact gradedLift_equivariant sourcePieces targetPieces lifts element value }
  refine ⟨lift, ?_, ?_⟩
  · have hinverse := gradedLift_rightInverse sourcePieces targetPieces lifts projection
      (fun degree value => congrArg Subtype.val (Classical.choose_spec (hlifts degree) value))
    intro value
    exact DFunLike.congr_fun hinverse value
  · intro degree value
    change gradedLift sourcePieces targetPieces lifts value.val ∈ _
    rw [gradedLift_piece]
    exact (lifts degree value).property

end Schubert.FiniteGroupCharacters
