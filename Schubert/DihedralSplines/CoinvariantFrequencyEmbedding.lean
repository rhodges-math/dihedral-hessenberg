import Schubert.DihedralSplines.LowDegreeCoinvariantInjection
import Schubert.DihedralSplines.QuotientSymmetry
import Schubert.DihedralSplines.DominanceEven
import Schubert.Dihedral.CoinvariantFrequency
import Schubert.Dihedral.SignTwist
import Mathlib.RingTheory.Flat.Basic

/-! # Coinvariant frequency embeddings in reflected quotient degrees -/

noncomputable section
open CategoryTheory
open scoped MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every lower interior frequency injects through the constant coinvariant map. -/
theorem lower_frequency_embedding (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : ℕ) (hpositive : 0 < degree) (hhalf : 2 * degree ≤ ideal.carrier.ncard) :
    ∃ embedding : Representation.IntertwiningMap (frequencyFDRep n degree).ρ
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective embedding := by
  have hbelow : degree < n := by
    have hcard := ideal.card_lt hproper
    omega
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    ⟨(Coinvariant.Middle.frequency_iso n hthree degree hpositive hbelow).some.symm⟩
  refine ⟨(ideal.toRootSubset.coinvariantPieceMap hthree degree).comp
    equivalence.toIntertwiningMap, ?_⟩
  exact (ideal.coinvariantPieceMap_injective degree hhalf degree le_rfl).comp
    equivalence.toLinearEquiv.injective

/-- Complementary sign duality carries a lower constant frequency into its upper degree. -/
theorem upper_frequency_embedding (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : ℕ) (hinterior : degree < ideal.carrier.ncard)
    (hhalf : ideal.carrier.ncard ≤ 2 * degree) :
    ∃ embedding : Representation.IntertwiningMap
        (frequencyFDRep n (ideal.carrier.ncard - degree : ℕ)).ρ
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective embedding := by
  let lower := ideal.carrier.ncard - degree
  have hpositive : 0 < lower := Nat.sub_pos_of_lt hinterior
  have hbound : 2 * lower ≤ ideal.carrier.ncard := by dsimp [lower]; omega
  obtain ⟨lowerMap, hlowerMap⟩ := lower_frequency_embedding ideal hproper lower hpositive hbound
  obtain ⟨sourceEquivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    ⟨(sign_frequency_iso n (lower : ℕ)).some.symm⟩
  obtain ⟨targetEquivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    (sign_complementary ideal degree hinterior.le)
  let tensorMap := (Representation.IntertwiningMap.id (signFDRep n).ρ).tensor lowerMap
  have htensorMap : Function.Injective tensorMap :=
    TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id hlowerMap
  refine ⟨targetEquivalence.toIntertwiningMap.comp
    (tensorMap.comp sourceEquivalence.toIntertwiningMap), ?_⟩
  exact targetEquivalence.toLinearEquiv.injective.comp
    (htensorMap.comp sourceEquivalence.toLinearEquiv.injective)

end Schubert.DihedralSplines.HessenbergIdeal.Right
