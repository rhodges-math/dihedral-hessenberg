import Schubert.FiniteGroupCharacters.GradedQuotientSection
import Schubert.DihedralSplines.SplinePieceSection

/-! # Graded sections of the geometric quotient actions -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- The coordinate quotient has a homogeneous equivariant section
into geometric splines. -/
theorem graded_section :
    ∃ lift : (representation selected hthree).IntertwiningMap
      (selected.splineRepresentation hthree),
      (∀ value, quotientMap selected hthree (lift value) = value) ∧
      ∀ degree (value : Quotient selected hthree), value ∈ piece selected hthree degree →
        lift value ∈ selected.piece degree := by
  let sourcePieces (degree : ℕ) : Subrepresentation (selected.splineRepresentation hthree) :=
    { toSubmodule := selected.piece degree
      apply_mem_toSubmodule := fun element value hvalue =>
        selected.dot_mem_piece hthree element degree value hvalue }
  let targetPieces (degree : ℕ) : Subrepresentation (representation selected hthree) :=
    { toSubmodule := piece selected hthree degree
      apply_mem_toSubmodule := fun element value hvalue =>
        dot_mem_piece selected hthree element degree value hvalue }
  let : GradedAlgebra (piece selected hthree) := gradedAlgebra selected hthree
  have hpieces : (fun degree => (targetPieces degree).toSubmodule) =
      piece selected hthree := rfl
  let : DirectSum.Decomposition (fun degree => (targetPieces degree).toSubmodule) :=
    hpieces.symm ▸ inferInstanceAs (DirectSum.Decomposition (piece selected hthree))
  let projection : (selected.splineRepresentation hthree).IntertwiningMap
      (representation selected hthree) :=
    { toLinearMap := (quotientMap selected hthree).toLinearMap
      isIntertwining' element := by
        apply LinearMap.ext
        intro value
        exact (dot_map selected hthree element value).symm }
  have hpiece : ∀ degree (value : (sourcePieces degree).toSubmodule),
      projection value.val ∈ (targetPieces degree).toSubmodule := by
    intro degree value
    exact (mem_piece selected hthree degree _).2 ⟨value.val, value.property, rfl⟩
  have hsurjective : ∀ degree (value : (targetPieces degree).toSubmodule),
      ∃ original : (sourcePieces degree).toSubmodule, projection original.val = value.val := by
    intro degree value
    obtain ⟨original, horiginal, hmap⟩ :=
      (mem_piece selected hthree degree value.val).1 value.property
    exact ⟨⟨original, horiginal⟩, hmap⟩
  obtain ⟨lift, hinverse, hhomogeneous⟩ :=
    Schubert.FiniteGroupCharacters.graded_quotient_section sourcePieces targetPieces
      projection hpiece hsurjective
  refine ⟨lift, hinverse, ?_⟩
  intro degree value hvalue
  exact hhomogeneous degree ⟨value, hvalue⟩

end Left

namespace Right

/-- The coordinate quotient has a homogeneous equivariant section
into geometric splines. -/
theorem graded_section :
    ∃ lift : (representation selected hthree).IntertwiningMap
      (selected.splineRepresentation hthree),
      (∀ value, quotientMap selected hthree (lift value) = value) ∧
      ∀ degree (value : Quotient selected hthree), value ∈ piece selected hthree degree →
        lift value ∈ selected.piece degree := by
  let sourcePieces (degree : ℕ) : Subrepresentation (selected.splineRepresentation hthree) :=
    { toSubmodule := selected.piece degree
      apply_mem_toSubmodule := fun element value hvalue =>
        selected.dot_mem_piece hthree element degree value hvalue }
  let targetPieces (degree : ℕ) : Subrepresentation (representation selected hthree) :=
    { toSubmodule := piece selected hthree degree
      apply_mem_toSubmodule := fun element value hvalue =>
        dot_mem_piece selected hthree element degree value hvalue }
  let : GradedAlgebra (piece selected hthree) := gradedAlgebra selected hthree
  have hpieces : (fun degree => (targetPieces degree).toSubmodule) =
      piece selected hthree := rfl
  let : DirectSum.Decomposition (fun degree => (targetPieces degree).toSubmodule) :=
    hpieces.symm ▸ inferInstanceAs (DirectSum.Decomposition (piece selected hthree))
  let projection : (selected.splineRepresentation hthree).IntertwiningMap
      (representation selected hthree) :=
    { toLinearMap := (quotientMap selected hthree).toLinearMap
      isIntertwining' element := by
        apply LinearMap.ext
        intro value
        exact (dot_map selected hthree element value).symm }
  have hpiece : ∀ degree (value : (sourcePieces degree).toSubmodule),
      projection value.val ∈ (targetPieces degree).toSubmodule := by
    intro degree value
    exact (mem_piece selected hthree degree _).2 ⟨value.val, value.property, rfl⟩
  have hsurjective : ∀ degree (value : (targetPieces degree).toSubmodule),
      ∃ original : (sourcePieces degree).toSubmodule, projection original.val = value.val := by
    intro degree value
    obtain ⟨original, horiginal, hmap⟩ :=
      (mem_piece selected hthree degree value.val).1 value.property
    exact ⟨⟨original, horiginal⟩, hmap⟩
  obtain ⟨lift, hinverse, hhomogeneous⟩ :=
    Schubert.FiniteGroupCharacters.graded_quotient_section sourcePieces targetPieces
      projection hpiece hsurjective
  refine ⟨lift, hinverse, ?_⟩
  intro degree value hvalue
  exact hhomogeneous degree ⟨value, hvalue⟩

end Right

end Schubert.Dihedral.RootSubset
