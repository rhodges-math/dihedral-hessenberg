import DihedralHessenberg.FiniteGroupCharacters.SimpleEmbedding
import DihedralHessenberg.Paper.QuotientSurvival

/-! # Simple constituent embeddings surviving coordinate projection -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- A strict constituent excess over the kernel yields a quotient embedding. -/
theorem constituent_survives (degree : ℕ) (test injected : FDRep ℂ (DihedralGroup n))
    [Simple test] (embedding : Representation.IntertwiningMap injected.ρ
      (ideal.toRootSubset.splinePieceRepresentation hthree degree))
    (hinjective : Function.Injective embedding)
    (hexcess : Module.finrank ℂ (test ⟶ removedFDRep ideal degree) <
      Module.finrank ℂ (test ⟶ injected)) :
    ∃ inclusion : Representation.IntertwiningMap test.ρ
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective inclusion := by
  apply simple_embedding_of_hom_pos test
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree)
  have hbound := quotient_survival ideal degree test injected embedding hinjective
  omega

/-- Paired middle coset constituents surviving the removed kernel
  inject into the quotient. -/
theorem middle_constituent (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (test : FDRep ℂ (DihedralGroup n)) [Simple test]
    (hexcess : Module.finrank ℂ (test ⟶ removedFDRep ideal half) <
      Module.finrank ℂ
        (test ⟶ (simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep)) :
    ∃ inclusion : Representation.IntertwiningMap test.ρ
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree half),
      Function.Injective inclusion := by
  apply simple_embedding_of_hom_pos test
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half)
  have hbound := middle_coset_survival ideal half hcard hproper first second test
  omega

end Left


namespace Right

/-- A strict constituent excess over the kernel yields a quotient embedding. -/
theorem constituent_survives (degree : ℕ) (test injected : FDRep ℂ (DihedralGroup n))
    [Simple test] (embedding : Representation.IntertwiningMap injected.ρ
      (ideal.toRootSubset.splinePieceRepresentation hthree degree))
    (hinjective : Function.Injective embedding)
    (hexcess : Module.finrank ℂ (test ⟶ removedFDRep ideal degree) <
      Module.finrank ℂ (test ⟶ injected)) :
    ∃ inclusion : Representation.IntertwiningMap test.ρ
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective inclusion := by
  apply simple_embedding_of_hom_pos test
    (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree)
  have hbound := quotient_survival ideal degree test injected embedding hinjective
  omega

/-- Paired middle coset constituents surviving the removed kernel
  inject into the quotient. -/
theorem middle_constituent (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (test : FDRep ℂ (DihedralGroup n)) [Simple test]
    (hexcess : Module.finrank ℂ (test ⟶ removedFDRep ideal half) <
      Module.finrank ℂ
        (test ⟶ (simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep)) :
    ∃ inclusion : Representation.IntertwiningMap test.ρ
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree half),
      Function.Injective inclusion := by
  apply simple_embedding_of_hom_pos test
    (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half)
  have hbound := middle_coset_survival ideal half hcard hproper first second test
  omega

end Right

end Schubert.DihedralSplines.HessenbergIdeal
