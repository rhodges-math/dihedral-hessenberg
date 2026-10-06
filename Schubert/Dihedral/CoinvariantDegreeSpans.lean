import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Schubert.Dihedral.CoinvariantHilbertFunction

/-! # Axial spans of coinvariant degree pieces

The two axial powers of an intermediate degree are independent quotient classes
and span its two-dimensional homogeneous piece.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The two intermediate axial quotient classes are linearly independent. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Middle.axial_independent (n : ℕ) [NeZero n] (hthree : 3
  ≤ n)
    (degree : ℕ) (hpositive : 0 < degree) (hbelow : degree < n) :
    LinearIndependent ℂ
      ![Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree),
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)] := by
  classical
  obtain ⟨basis, hbasis⟩ := exists_coinvariant_axial_basis n hthree
  let indices (coordinate : Fin 2) : Fin n × Fin 2 :=
    if coordinate = 0 then (⟨n - degree, by omega⟩, 0) else (⟨degree, hbelow⟩, 1)
  have hsnd (coordinate : Fin 2) : (indices coordinate).2 = coordinate := by
    fin_cases coordinate <;> rfl
  have hinjective : Function.Injective indices := by
    intro first second hequal
    simpa only [hsnd] using congrArg Prod.snd hequal
  have hfamily : (fun coordinate => basis (indices coordinate)) =
      ![Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree),
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)] := by
    funext coordinate
    fin_cases coordinate
    · have hcomplement : n - degree ≠ 0 := by omega
      rw [hbasis]
      simp [indices, hcomplement, Nat.sub_sub_self hbelow.le]
    · rw [hbasis]
      simp [indices, hpositive.ne']
  rw [← hfamily]
  exact basis.linearIndependent.comp indices hinjective

/-- The intermediate coinvariant degree piece is spanned by the two axial powers of that degree. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.eq_span_middle (n : ℕ) [NeZero n] (hthree : 3 ≤
  n)
    (degree : ℕ) (hpositive : 0 < degree) (hbelow : degree < n) :
    TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
      (coinvariantIdeal n) degree =
      Submodule.span ℂ {Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree),
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)} := by
  have := coinvariant_homogeneousPiece_finite n degree
  have hle : Submodule.span ℂ
      {Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree),
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)} ≤
      TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
        (coinvariantIdeal n) degree := by
    apply Submodule.span_le.mpr
    intro value hvalue
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvalue
    rcases hvalue with rfl | rfl
    · apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
      simpa using auxiliaryU_isHomogeneous.pow degree
    · apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
      simpa using auxiliaryV_isHomogeneous.pow degree
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [_root_.Schubert.Dihedral.Coinvariant.Piece.finrank_middle n hthree degree hpositive hbelow]
  have hLI := _root_.Schubert.Dihedral.Coinvariant.Middle.axial_independent n hthree degree
    hpositive hbelow
  have hrange : Set.range
      ![Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree),
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)] =
      {Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree),
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)} := by
    ext value
    simp [or_comm]
  rw [← hrange, Module.finrank_eq_card_basis (Module.Basis.span hLI)]
  exact Fintype.card_fin 2

/-- The constant coinvariant class is nonzero. -/
theorem coinvariant_one_ne_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    (1 : CoinvariantAlgebra n) ≠ 0 := by
  obtain ⟨basis, hbasis⟩ := exists_coinvariant_axial_basis n hthree
  have hnonzero := basis.ne_zero (⟨0, by omega⟩, 0)
  simpa [hbasis] using hnonzero

/-- The top axial power represents a nonzero coinvariant class. -/
theorem coinvariant_top_axial_ne_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n) ≠ 0 := by
  obtain ⟨basis, hbasis⟩ := exists_coinvariant_axial_basis n hthree
  have hnonzero := basis.ne_zero (⟨0, by omega⟩, 1)
  simpa [hbasis] using hnonzero

/-- The constant coinvariant piece is the span of the identity class. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Piece.eq_span_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
  :
    TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
      (coinvariantIdeal n) 0 = Submodule.span ℂ {(1 : CoinvariantAlgebra n)} := by
  have := coinvariant_homogeneousPiece_finite n 0
  have hle : Submodule.span ℂ {(1 : CoinvariantAlgebra n)} ≤
      TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
        (coinvariantIdeal n) 0 := by
    apply Submodule.span_le.mpr
    intro value hvalue
    obtain rfl := Set.mem_singleton_iff.mp hvalue
    exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
      (MvPolynomial.isHomogeneous_one (Fin 2) ℂ)
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [_root_.Schubert.Dihedral.Coinvariant.Piece.finrank_zero n hthree,
    finrank_span_singleton (coinvariant_one_ne_zero n hthree)]

/-- The top coinvariant piece is the span of the top axial power. -/
theorem coinvariant_homogeneousPiece_eq_span_top (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
      (coinvariantIdeal n) n =
      Submodule.span ℂ {Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n)} := by
  have := coinvariant_homogeneousPiece_finite n n
  have hle : Submodule.span ℂ {Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n)} ≤
      TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
        (coinvariantIdeal n) n := by
    apply Submodule.span_le.mpr
    intro value hvalue
    obtain rfl := Set.mem_singleton_iff.mp hvalue
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    simpa using auxiliaryU_isHomogeneous.pow n
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [coinvariant_homogeneousPiece_finrank_top n hthree,
    finrank_span_singleton (coinvariant_top_axial_ne_zero n hthree)]

end Schubert.Dihedral
