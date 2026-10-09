import Mathlib.RepresentationTheory.Character

/-! # Characters calculated in eigenvector and interchange bases

These formulas reduce character evaluation to the diagonal entries of the matrix in
an explicit finite basis, without introducing a new representation carrier.
-/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- The character in a finite eigenbasis is the sum of the corresponding eigenvalues. -/
theorem _root_.Schubert.FiniteGroupCharacters.Eigenbasis.character_eq_sum
    {K G V I : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    [Fintype I] (representation : Representation K G V)
    (basis : Module.Basis I K V) (element : G) (eigenvalues : I → K)
    (heigenvalues : ∀ index, representation element (basis index) =
      eigenvalues index • basis index) :
    representation.character element = ∑ index, eigenvalues index := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K basis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, heigenvalues]

/-- An operator interchanging two basis lines has zero character. -/
theorem representation_character_eq_zero_of_swap
    {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    (representation : Representation K G V)
    (basis : Module.Basis (Fin 2) K V) (element : G) (first second : K)
    (hfirst : representation element (basis 0) = first • basis 1)
    (hsecond : representation element (basis 1) = second • basis 0) :
    representation.character element = 0 := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K basis]
  simp [Matrix.trace, Fin.sum_univ_two, LinearMap.toMatrix_apply, hfirst, hsecond]

end Schubert.FiniteGroupCharacters
