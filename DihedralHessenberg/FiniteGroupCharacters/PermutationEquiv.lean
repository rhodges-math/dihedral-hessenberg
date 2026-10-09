import TauCeti.RepresentationTheory.AsModule
import Mathlib.RepresentationTheory.Equiv

/-! # Linearization of equivariant permutation bijections -/

noncomputable section

open CategoryTheory

namespace Schubert.FiniteGroupCharacters

universe u v

/-- An equivariant bijection gives the standard reindexing equivalence of permutation actions. -/
def permutationEquiv {K G X Y : Type*} [Field K] [Monoid G] [MulAction G X] [MulAction G Y]
    (equivalence : X ≃ Y)
    (hequivariant : ∀ (element : G) (value : X),
      equivalence (element • value) = element • equivalence value) :
    (Representation.ofMulAction K G X).Equiv (Representation.ofMulAction K G Y) := by
  refine Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv K K equivalence) ?_
  intro element
  refine MonoidAlgebra.lhom_ext' fun value => LinearMap.ext_ring ?_
  change MonoidAlgebra.mapDomainLinearEquiv K K equivalence
      ((Representation.ofMulAction K G X) element (MonoidAlgebra.single value 1)) =
    (Representation.ofMulAction K G Y) element
      (MonoidAlgebra.mapDomainLinearEquiv K K equivalence (MonoidAlgebra.single value 1))
  rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearEquiv_single,
    MonoidAlgebra.mapDomainLinearEquiv_single, Representation.ofMulAction_single,
    hequivariant]

/-- Finite equivariant permutation sets give standard FDRep isomorphisms. -/
theorem permutation_iso {K X Y : Type u} {G : Type v} [Field K] [Monoid G]
    [MulAction G X] [MulAction G Y]
    [Finite X] [Finite Y] (equivalence : X ≃ Y)
    (hequivariant : ∀ (element : G) (value : X),
      equivalence (element • value) = element • equivalence value) :
    Nonempty (FDRep.of (Representation.ofMulAction K G X) ≅
      FDRep.of (Representation.ofMulAction K G Y)) := by
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact ⟨permutationEquiv equivalence hequivariant⟩

end Schubert.FiniteGroupCharacters
