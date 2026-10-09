import DihedralHessenberg.FiniteGroupCharacters.CharacterExpansion
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exact constituent exhaustion by a positive dimension budget -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.FiniteGroupCharacters.SimpleFamily
variable {K G I : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Group G] [Finite G] [Fintype I]

/-- Positive dimension weights make any saturated multiplicity lower bounds exact. -/
theorem multiplicities_exhausted (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card I = Nat.card (ConjClasses G)) (source : FDRep K G)
    (lower : I → ℕ) (hpositive : ∀ index, 0 < Module.finrank K (family index))
    (hlower : ∀ index, lower index ≤ Module.finrank K (family index ⟶ source))
    (hbudget : ∑ index, lower index * Module.finrank K (family index) =
      Module.finrank K source) :
    ∀ index, Module.finrank K (family index ⟶ source) = lower index := by
  classical
  have hsum : ∑ index, lower index * Module.finrank K (family index) =
      ∑ index, Module.finrank K (family index ⟶ source) *
        Module.finrank K (family index) :=
    hbudget.trans (dimension_sum family hsimple hdistinct hcard source)
  have hequal := (Finset.sum_eq_sum_iff_of_le (fun index (_ : index ∈ Finset.univ) =>
    Nat.mul_le_mul_right (Module.finrank K (family index)) (hlower index))).mp hsum
  intro index
  exact (Nat.mul_right_cancel (hpositive index) (hequal index (Finset.mem_univ index))).symm

end Schubert.FiniteGroupCharacters.SimpleFamily
