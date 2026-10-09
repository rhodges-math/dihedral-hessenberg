import DihedralHessenberg.FiniteGroupCharacters.PermutationSpan
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.SumProd
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # Permutation representations on disjoint unions -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G I J : Type*} [Field K] [Monoid G] [MulAction G I] [MulAction G J]

/-- Splitting a disjoint union gives the product of its permutation actions. -/
def permutationSumEquiv :
    Representation.Equiv (Representation.ofMulAction K G (I ⊕ J))
      ((Representation.ofMulAction K G I).prod (Representation.ofMulAction K G J)) := by
  let splitting : MonoidAlgebra K (I ⊕ J) ≃ₗ[K]
      MonoidAlgebra K I × MonoidAlgebra K J :=
    (MonoidAlgebra.coeffLinearEquiv K).trans
      ((Finsupp.sumFinsuppLEquivProdFinsupp K).trans
        ((MonoidAlgebra.coeffLinearEquiv K).symm.prodCongr
          (MonoidAlgebra.coeffLinearEquiv K).symm))
  refine Representation.Equiv.mk splitting ?_
  intro element
  refine MonoidAlgebra.lhom_ext' fun index => LinearMap.ext_ring ?_
  cases index with
  | inl index =>
    change splitting ((Representation.ofMulAction K G (I ⊕ J)) element
        (MonoidAlgebra.single (Sum.inl index) 1)) =
      ((Representation.ofMulAction K G I).prod (Representation.ofMulAction K G J)) element
        (splitting (MonoidAlgebra.single (Sum.inl index) 1))
    simp [splitting, Representation.ofMulAction_single, Representation.prod,
      MonoidAlgebra.coeff_single, Finsupp.sumFinsuppLEquivProdFinsupp,
      Finsupp.sumFinsuppAddEquivProdFinsupp, Finsupp.sumFinsuppEquivProdFinsupp]
  | inr index =>
    change splitting ((Representation.ofMulAction K G (I ⊕ J)) element
        (MonoidAlgebra.single (Sum.inr index) 1)) =
      ((Representation.ofMulAction K G I).prod (Representation.ofMulAction K G J)) element
        (splitting (MonoidAlgebra.single (Sum.inr index) 1))
    simp [splitting, Representation.ofMulAction_single, Representation.prod,
      MonoidAlgebra.coeff_single, Finsupp.sumFinsuppLEquivProdFinsupp,
      Finsupp.sumFinsuppAddEquivProdFinsupp, Finsupp.sumFinsuppEquivProdFinsupp]

end Schubert.FiniteGroupCharacters

namespace Schubert.FiniteGroupCharacters.PermutationSpan
variable {K G I J V : Type*} [Field K] [Monoid G] [MulAction G I] [MulAction G J]
variable [AddCommGroup V] [Module K V]

/-- Joint independence identifies both permutation factors with their combined span. -/
def pairedEquiv (source : Representation K G V) (first : I → V) (second : J → V)
    (hfirst : ∀ element index, source element (first index) = first (element • index))
    (hsecond : ∀ element index, source element (second index) = second (element • index))
    (hindependent : LinearIndependent K (Sum.elim first second)) :
    Representation.Equiv
      ((Representation.ofMulAction K G I).prod (Representation.ofMulAction K G J))
      (action source (Sum.elim first second) (fun element index => by
        cases index with
        | inl index => exact hfirst element index
        | inr index => exact hsecond element index)) :=
  permutationSumEquiv.symm.trans
    (equiv source (Sum.elim first second) (fun element index => by
      cases index with
      | inl index => exact hfirst element index
      | inr index => exact hsecond element index) hindependent)

end Schubert.FiniteGroupCharacters.PermutationSpan

open CategoryTheory Limits
namespace Schubert.FiniteGroupCharacters
variable {G : Type} [Group G] [Finite G]

/-- A finite direct product is the categorical biproduct of the same representations. -/
theorem product_iso {V W : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (first : Representation ℂ G V) (second : Representation ℂ G W) :
    Nonempty (FDRep.of (first.prod second) ≅ (FDRep.of first ⊞ FDRep.of second)) := by
  classical
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_biprod, Pi.add_apply]
  change LinearMap.trace ℂ (V × W) ((first element).prodMap (second element)) =
    LinearMap.trace ℂ V (first element) + LinearMap.trace ℂ W (second element)
  exact LinearMap.trace_prodMap' _ _

end Schubert.FiniteGroupCharacters

namespace Schubert.FiniteGroupCharacters.PermutationSpan
variable {G I J V : Type} [Group G] [Finite G] [MulAction G I] [MulAction G J]
variable [Finite I] [Finite J] [AddCommGroup V] [Module ℂ V]

/-- Both finite permutation objects jointly represent their independent combined span. -/
theorem paired_iso (source : Representation ℂ G V) (first : I → V) (second : J → V)
    (hfirst : ∀ element index, source element (first index) = first (element • index))
    (hsecond : ∀ element index, source element (second index) = second (element • index))
    (hindependent : LinearIndependent ℂ (Sum.elim first second)) :
    Nonempty ((FDRep.of (Representation.ofMulAction ℂ G I) ⊞
      FDRep.of (Representation.ofMulAction ℂ G J)) ≅
      fdRep source (Sum.elim first second) (fun element index => by
        cases index with
        | inl index => exact hfirst element index
        | inr index => exact hsecond element index) hindependent) := by
  obtain ⟨product⟩ := product_iso
    (Representation.ofMulAction ℂ G I) (Representation.ofMulAction ℂ G J)
  have hspan : Nonempty (FDRep.of
      ((Representation.ofMulAction ℂ G I).prod (Representation.ofMulAction ℂ G J)) ≅
      fdRep source (Sum.elim first second) (fun element index => by
        cases index with
        | inl index => exact hfirst element index
        | inr index => exact hsecond element index) hindependent) := by
    apply TauCeti.nonempty_fdRepIso_iff.mpr
    exact ⟨pairedEquiv source first second hfirst hsecond hindependent⟩
  obtain ⟨span⟩ := hspan
  exact ⟨product.symm ≪≫ span⟩

end Schubert.FiniteGroupCharacters.PermutationSpan
