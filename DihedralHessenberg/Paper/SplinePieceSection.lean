import DihedralHessenberg.FiniteGroupCharacters.EquivariantSection
import DihedralHessenberg.Paper.QuotientRepresentation

/-! # Equivariant homogeneous sections of the geometric spline quotients -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

/-- The complex dot representation on geometric splines. -/
def splineRepresentation : Representation ℂ (DihedralGroup n) selected.Spline :=
  (AlgEquiv.toLinearMapHom ℂ _).comp (selected.dotAction hthree)

/-- The dot representation restricted to a pointwise homogeneous spline piece. -/
def splinePieceRepresentation (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (selected.piece degree) :=
  (selected.splineRepresentation hthree).subrepresentation (selected.piece degree)
    fun element value hvalue => selected.dot_mem_piece hthree element degree value hvalue

namespace Left

/-- The left quotient projection restricts to an intertwiner in every degree. -/
def pieceProjection (degree : ℕ) :
    Representation.IntertwiningMap (selected.splinePieceRepresentation hthree degree)
      (pieceRepresentation selected hthree degree) where
  toLinearMap :=
    { toFun := fun value => ⟨quotientMap selected hthree value.val,
        (mem_piece selected hthree degree _).2 ⟨value.val, value.property, rfl⟩⟩
      map_add' := fun first second => Subtype.ext (map_add _ first.val second.val)
      map_smul' := fun scalar value => Subtype.ext (map_smul _ scalar value.val) }
  isIntertwining' element := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    exact (dot_map selected hthree element value.val).symm

/-- Every left quotient degree admits an equivariant section into homogeneous splines. -/
theorem piece_section (degree : ℕ) :
    ∃ lift : Representation.IntertwiningMap (pieceRepresentation selected hthree degree)
      (selected.splinePieceRepresentation hthree degree),
      ∀ value, pieceProjection selected hthree degree (lift value) = value := by
  refine Schubert.FiniteGroupCharacters.equivariant_section
    (K := ℂ) (G := DihedralGroup n) (V := selected.piece degree)
    (W := piece selected hthree degree)
    (source := selected.splinePieceRepresentation hthree degree)
    (target := pieceRepresentation selected hthree degree)
    (pieceProjection selected hthree degree) ?_
  intro value
  obtain ⟨original, horiginal, hmap⟩ :=
    (mem_piece selected hthree degree value.val).1 value.property
  exact ⟨⟨original, horiginal⟩, Subtype.ext hmap⟩

end Left

namespace Right

/-- The right quotient projection restricts to an intertwiner in every degree. -/
def pieceProjection (degree : ℕ) :
    Representation.IntertwiningMap (selected.splinePieceRepresentation hthree degree)
      (pieceRepresentation selected hthree degree) where
  toLinearMap :=
    { toFun := fun value => ⟨quotientMap selected hthree value.val,
        (mem_piece selected hthree degree _).2 ⟨value.val, value.property, rfl⟩⟩
      map_add' := fun first second => Subtype.ext (map_add _ first.val second.val)
      map_smul' := fun scalar value => Subtype.ext (map_smul _ scalar value.val) }
  isIntertwining' element := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    exact (dot_map selected hthree element value.val).symm

/-- Every right quotient degree admits an equivariant section into homogeneous splines. -/
theorem piece_section (degree : ℕ) :
    ∃ lift : Representation.IntertwiningMap (pieceRepresentation selected hthree degree)
      (selected.splinePieceRepresentation hthree degree),
      ∀ value, pieceProjection selected hthree degree (lift value) = value := by
  refine Schubert.FiniteGroupCharacters.equivariant_section
    (K := ℂ) (G := DihedralGroup n) (V := selected.piece degree)
    (W := piece selected hthree degree)
    (source := selected.splinePieceRepresentation hthree degree)
    (target := pieceRepresentation selected hthree degree)
    (pieceProjection selected hthree degree) ?_
  intro value
  obtain ⟨original, horiginal, hmap⟩ :=
    (mem_piece selected hthree degree value.val).1 value.property
  exact ⟨⟨original, horiginal⟩, Subtype.ext hmap⟩

end Right

end Schubert.Dihedral.RootSubset
