import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Basic
import Schubert.Dihedral.InvariantRotationBlocks
import Schubert.Dihedral.InvariantSpanning

/-! # Freeness over the dihedral invariant algebra

The axial rotation blocks form a basis of the polynomial algebra over its
invariant algebra. Their cardinality is the dihedral order 2n.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The axial rotation blocks span the polynomial algebra over the invariants. -/
theorem invariant_axial_rotation_blocks_span (n : ℕ) [NeZero n] :
    Submodule.span (invariantSubalgebra n) (Set.range (fun index : Fin n × Fin 2 =>
      (if index.1.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
        else ![auxiliaryU ^ (n - index.1.val), auxiliaryV ^ index.1.val]) index.2)) = ⊤ := by
  classical
  have hpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  apply _root_.Schubert.Dihedral.Invariants.span_eq_top_of_axial_powers
  · intro degree hdegree
    apply Submodule.subset_span
    by_cases hzero : degree = 0
    · subst degree
      refine ⟨(⟨0, hpositive⟩, 0), ?_⟩
      simp
    by_cases htop : degree = n
    · subst degree
      refine ⟨(⟨0, hpositive⟩, 1), ?_⟩
      simp
    refine ⟨(⟨n - degree, by omega⟩, 0), ?_⟩
    have hnonzero : n - degree ≠ 0 := by omega
    simp only [hnonzero, ite_false, Matrix.cons_val_zero]
    congr 1
    omega
  · intro degree hdegree
    apply Submodule.subset_span
    by_cases hzero : degree = 0
    · subst degree
      refine ⟨(⟨0, hpositive⟩, 0), ?_⟩
      simp
    refine ⟨(⟨degree, hdegree⟩, 1), ?_⟩
    simp [hzero]

/-- There is an invariant-module basis consisting of the axial rotation blocks. -/
theorem exists_invariant_axial_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis (Fin n × Fin 2) (invariantSubalgebra n) CoordinatePolynomial,
      ∀ index, basis index =
        (if index.1.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
          else ![auxiliaryU ^ (n - index.1.val), auxiliaryV ^ index.1.val]) index.2 := by
  let basis := Module.Basis.mk (_root_.Schubert.Dihedral.Invariants.axial_blocks_independent n
    hthree)
    (by rw [invariant_axial_rotation_blocks_span])
  exact ⟨basis, fun index => Module.Basis.mk_apply _ _ index⟩

/-- The coordinate polynomial algebra is free over its invariant algebra. -/
theorem _root_.Schubert.Dihedral.Invariants.polynomial_free (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Module.Free (invariantSubalgebra n) CoordinatePolynomial := by
  obtain ⟨basis, _⟩ := exists_invariant_axial_basis n hthree
  exact Module.Free.of_basis basis

/-- The invariant-module rank of the polynomial algebra is exactly 2n. -/
theorem _root_.Schubert.Dihedral.Invariants.polynomial_finrank (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) : Module.finrank (invariantSubalgebra n) CoordinatePolynomial = 2 * n := by
  obtain ⟨basis, _⟩ := exists_invariant_axial_basis n hthree
  rw [Module.finrank_eq_card_basis basis, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  omega

end Schubert.Dihedral
