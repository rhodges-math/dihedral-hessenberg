import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.Module

/-! # Stable subspaces for two-dimensional diagonal and interchange operators

Distinct eigenvalues separate two basis coordinates. An operator interchanging the
basis lines with nonzero coefficients then eliminates every proper nonzero stable subspace.
-/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- Two separated eigenlines interchanged by a second operator have no proper stable subspace. -/
theorem _root_.Schubert.FiniteGroupCharacters.DiagonalSwap.submodule_eq_bot_or_top
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (basis : Module.Basis (Fin 2) K V) (diagonal swap : Module.End K V)
    (firstEigen secondEigen firstSwap secondSwap : K)
    (heigen : firstEigen ≠ secondEigen) (hfirstSwap : firstSwap ≠ 0)
    (hsecondSwap : secondSwap ≠ 0)
    (hdiagonalFirst : diagonal (basis 0) = firstEigen • basis 0)
    (hdiagonalSecond : diagonal (basis 1) = secondEigen • basis 1)
    (hswapFirst : swap (basis 0) = firstSwap • basis 1)
    (hswapSecond : swap (basis 1) = secondSwap • basis 0)
    (subspace : Submodule K V)
    (hdiagonal : ∀ vector ∈ subspace, diagonal vector ∈ subspace)
    (hswap : ∀ vector ∈ subspace, swap vector ∈ subspace) :
    subspace = ⊥ ∨ subspace = ⊤ := by
  classical
  by_cases hbot : subspace = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨vector, hvector, hnonzero⟩ := subspace.ne_bot_iff.mp hbot
    let firstCoordinate := basis.repr vector 0
    let secondCoordinate := basis.repr vector 1
    have hcoordinates : firstCoordinate • basis 0 +
        secondCoordinate • basis 1 = vector := by
      simpa only [Fin.sum_univ_two] using basis.sum_repr vector
    have hfirst : basis 0 ∈ subspace ∨ basis 1 ∈ subspace := by
      by_cases hzero : firstCoordinate = 0
      · right
        have hsecond : secondCoordinate ≠ 0 := by
          intro hequal
          simp [hzero, hequal] at hcoordinates
          exact hnonzero hcoordinates.symm
        apply (subspace.smul_mem_iff hsecond).mp
        have hmem := hvector
        rw [← hcoordinates] at hmem
        simpa [hzero] using hmem
      · left
        have hproject : diagonal vector - secondEigen • vector =
            (firstCoordinate * (firstEigen - secondEigen)) • basis 0 := by
          rw [← hcoordinates, map_add, map_smul, map_smul,
            hdiagonalFirst, hdiagonalSecond]
          module
        apply (subspace.smul_mem_iff (mul_ne_zero hzero (sub_ne_zero.mpr heigen))).mp
        rw [← hproject]
        exact subspace.sub_mem (hdiagonal vector hvector)
          (subspace.smul_mem secondEigen hvector)
    have hboth : basis 0 ∈ subspace ∧ basis 1 ∈ subspace := by
      rcases hfirst with hfirst | hsecond
      · refine ⟨hfirst, (subspace.smul_mem_iff hfirstSwap).mp ?_⟩
        rw [← hswapFirst]
        exact hswap (basis 0) hfirst
      · refine ⟨(subspace.smul_mem_iff hsecondSwap).mp ?_, hsecond⟩
        rw [← hswapSecond]
        exact hswap (basis 1) hsecond
    apply top_unique
    rw [← basis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    fin_cases index
    · exact hboth.1
    · exact hboth.2

/-- A two-dimensional representation with separated eigenlines and interchange is irreducible. -/
theorem _root_.Schubert.FiniteGroupCharacters.DiagonalSwap.irreducible
    {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    (representation : Representation K G V) (basis : Module.Basis (Fin 2) K V)
    (rotation reflection : G) (firstEigen secondEigen firstSwap secondSwap : K)
    (heigen : firstEigen ≠ secondEigen) (hfirstSwap : firstSwap ≠ 0)
    (hsecondSwap : secondSwap ≠ 0)
    (hdiagonalFirst : representation rotation (basis 0) = firstEigen • basis 0)
    (hdiagonalSecond : representation rotation (basis 1) = secondEigen • basis 1)
    (hswapFirst : representation reflection (basis 0) = firstSwap • basis 1)
    (hswapSecond : representation reflection (basis 1) = secondSwap • basis 0) :
    Representation.IsIrreducible representation := by
  have hdistinct : (⊥ : Subrepresentation representation) ≠ ⊤ := by
    intro hequal
    have hsubmodule := congrArg Subrepresentation.toSubmodule hequal
    change (⊥ : Submodule K V) = ⊤ at hsubmodule
    have hmem : basis 0 ∈ (⊥ : Submodule K V) := by
      rw [hsubmodule]
      exact Submodule.mem_top
    exact basis.ne_zero 0 hmem
  let := nontrivial_of_ne (⊥ : Subrepresentation representation) ⊤ hdistinct
  apply IsSimpleOrder.of_forall_eq_top
  intro subrepresentation hnonzero
  have hdichotomy := _root_.Schubert.FiniteGroupCharacters.DiagonalSwap.submodule_eq_bot_or_top
    basis
    (representation rotation) (representation reflection)
    firstEigen secondEigen firstSwap secondSwap heigen hfirstSwap hsecondSwap
    hdiagonalFirst hdiagonalSecond hswapFirst hswapSecond subrepresentation.toSubmodule
    (fun vector hvector => subrepresentation.apply_mem_toSubmodule rotation hvector)
    (fun vector hvector => subrepresentation.apply_mem_toSubmodule reflection hvector)
  rcases hdichotomy with hbot | htop
  · exact (hnonzero (Subrepresentation.toSubmodule_injective hbot)).elim
  · exact Subrepresentation.toSubmodule_injective htop

end Schubert.FiniteGroupCharacters
