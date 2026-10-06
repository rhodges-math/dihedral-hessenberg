import Schubert.FiniteGroupCharacters.PermutationEquiv
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Linearization of equivariant independent families in their spans -/

noncomputable section
namespace Schubert.FiniteGroupCharacters.PermutationSpan

variable {K G I V : Type*} [CommRing K] [Monoid G] [MulAction G I]
variable [AddCommGroup V] [Module K V]

/-- The representation restricted to the span of an equivariant indexed family. -/
def action (source : Representation K G V) (family : I → V)
    (hequivariant : ∀ element index, source element (family index) = family (element • index)) :
    Representation K G (Submodule.span K (Set.range family)) :=
  source.subrepresentation (Submodule.span K (Set.range family)) (fun element value hvalue => by
    change source element value ∈ Submodule.span K (Set.range family)
    induction hvalue using Submodule.span_induction with
    | mem value hvalue =>
        obtain ⟨index, rfl⟩ := hvalue
        rw [hequivariant]
        exact Submodule.subset_span ⟨element • index, rfl⟩
    | zero => simp
    | add first second _ _ hfirst hsecond =>
        simpa only [map_add] using Submodule.add_mem _ hfirst hsecond
    | smul scalar value _ hvalue =>
        simpa only [map_smul] using Submodule.smul_mem _ scalar hvalue)

/-- An independent equivariant family linearizes to the permutation representation. -/
def equiv (source : Representation K G V) (family : I → V)
    (hequivariant : ∀ element index, source element (family index) = family (element • index))
    (hindependent : LinearIndependent K family) :
    Representation.Equiv (Representation.ofMulAction K G I) (action source family hequivariant) :=
      by
  let basis := Module.Basis.span hindependent
  refine Representation.Equiv.mk ((MonoidAlgebra.coeffLinearEquiv K).trans basis.repr.symm) ?_
  intro element
  refine MonoidAlgebra.lhom_ext' fun index => LinearMap.ext_ring ?_
  change basis.repr.symm (((Representation.ofMulAction K G I) element
    (MonoidAlgebra.single index 1)).coeff) =
      (action source family hequivariant) element (basis.repr.symm (Finsupp.single index 1))
  rw [Representation.ofMulAction_single, MonoidAlgebra.coeff_single,
    Module.Basis.repr_symm_single_one,
    Module.Basis.repr_symm_single_one]
  apply Subtype.ext
  change (basis (element • index)).val = source element (basis index).val
  rw [Module.Basis.coe_span_apply, Module.Basis.coe_span_apply]
  exact (hequivariant element index).symm

/-- Each permutation delta maps to its indexed vector. -/
theorem equiv_single (source : Representation K G V) (family : I → V)
    (hequivariant : ∀ element index, source element (family index) = family (element • index))
    (hindependent : LinearIndependent K family) (index : I) :
    (equiv source family hequivariant hindependent (MonoidAlgebra.single index 1)).val =
      family index := by
  change ((Module.Basis.span hindependent).repr.symm
    (Finsupp.single index 1)).val = family index
  rw [Module.Basis.repr_symm_single_one, Module.Basis.coe_span_apply]

end Schubert.FiniteGroupCharacters.PermutationSpan

namespace Schubert.FiniteGroupCharacters.PermutationSpan
universe u v

/-- A finite independent orbit span is a standard finite representation object. -/
def fdRep {K I V : Type u} {G : Type v} [Field K] [Monoid G] [MulAction G I]
    [AddCommGroup V] [Module K V] [Finite I]
    (source : Representation K G V) (family : I → V)
    (hequivariant : ∀ element index, source element (family index) = family (element • index))
    (hindependent : LinearIndependent K family) : FDRep K G := by
  let : AddCommGroup (Submodule.span K (Set.range family)) := Submodule.addCommGroup _
  let : Module K (Submodule.span K (Set.range family)) := Submodule.module _
  let := Module.Finite.of_basis (Module.Basis.span hindependent)
  exact FDRep.of (V := Submodule.span K (Set.range family)) (action source family hequivariant)

/-- A finite independent family gives a permutation-object isomorphism onto its span. -/
theorem iso {K I V : Type u} {G : Type v} [Field K] [Monoid G] [MulAction G I]
    [AddCommGroup V] [Module K V] [Finite I]
    (source : Representation K G V) (family : I → V)
    (hequivariant : ∀ element index, source element (family index) = family (element • index))
    (hindependent : LinearIndependent K family) :
    Nonempty (FDRep.of (Representation.ofMulAction K G I) ≅
      fdRep source family hequivariant hindependent) := by
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact ⟨equiv source family hequivariant hindependent⟩

end Schubert.FiniteGroupCharacters.PermutationSpan
