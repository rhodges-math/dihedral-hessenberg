import DihedralHessenberg.Dihedral.CoinvariantGradedRepresentation
import DihedralHessenberg.Dihedral.CoinvariantDegreeSpans

/-! # Axial bases of the middle coinvariant degree representations

For each degree strictly between zero and the rotation order, the classes of u^d
and v^d are a basis of the existing homogeneous quotient piece.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every middle coinvariant degree has the two axial classes as a basis. -/
theorem exists_coinvariant_middle_piece_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (hpositive : 0 < degree) (hbelow : degree < n) :
    ∃ basis : Module.Basis (Fin 2) ℂ (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree),
      (basis 0 : CoinvariantAlgebra n) =
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree) ∧
      (basis 1 : CoinvariantAlgebra n) =
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree) := by
  let piece := TauCeti.GradedAlgebra.quotientPiece
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree
  have hU : Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree) ∈ piece := by
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    simpa using auxiliaryU_isHomogeneous.pow degree
  have hV : Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree) ∈ piece := by
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    simpa using auxiliaryV_isHomogeneous.pow degree
  let vectors : Fin 2 → piece :=
    ![⟨Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree), hU⟩,
      ⟨Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree), hV⟩]
  have hLI : LinearIndependent ℂ vectors := by
    apply LinearIndependent.of_comp piece.subtype
    convert _root_.Schubert.Dihedral.Coinvariant.Middle.axial_independent n hthree degree hpositive
      hbelow using 1
    funext index
    fin_cases index <;> rfl
  have hrank : Fintype.card (Fin 2) = Module.finrank ℂ piece := by
    rw [_root_.Schubert.Dihedral.Coinvariant.Piece.finrank_middle n hthree degree hpositive hbelow]
    rfl
  let basis := Module.Basis.mk hLI (hLI.span_eq_top_of_card_eq_finrank hrank).ge
  refine ⟨basis, ?_, ?_⟩
  · exact congrArg Subtype.val (Module.Basis.mk_apply _ _ 0)
  · exact congrArg Subtype.val (Module.Basis.mk_apply _ _ 1)

end Schubert.Dihedral
