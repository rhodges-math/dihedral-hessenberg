import TauCeti.RepresentationTheory.RepresentationRing.Basic

/-! # Characters of finite biproducts -/

noncomputable section

open CategoryTheory Limits
open scoped BigOperators

namespace Schubert.FiniteGroupCharacters

/-- Standard finite-dimensional representations have finite biproducts. -/
instance finiteBiproducts {K G : Type*} [Field K] [Monoid G] :
    HasFiniteBiproducts (FDRep K G) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The character of a finite biproduct is the sum of the summand characters. -/
theorem finiteSum_character {K G : Type*} {I : Type} [Field K] [Monoid G] [Fintype I]
    (family : I → FDRep K G) : (⨁ family).character = ∑ index, (family index).character := by
  have hclass : (TauCeti.SplitK0.of (⨁ family) : TauCeti.repRing K G) =
      ∑ index, TauCeti.SplitK0.of (family index) := TauCeti.SplitK0.of_biproduct family
  have htrace := congrArg (TauCeti.repRingCharacter K G) hclass
  simpa only [map_sum, TauCeti.repRingCharacter_of] using htrace

end Schubert.FiniteGroupCharacters
