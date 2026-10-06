import Schubert.FiniteGroupCharacters.MorphismDimension
import Schubert.FiniteGroupCharacters.HomDimension
import Schubert.FiniteGroupCharacters.HomIntertwiner
import Schubert.DihedralSplines.LeftFixedRepresentation
import Schubert.FiniteGroupCharacters.MorphismEmbedding

/-! # Fixed constituents at the quotient boundary -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Two fixed full-quotient classes survive at every positive boundary degree. -/
theorem boundary_trivial_bound (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 0 < half) :
    2 ≤ Module.finrank ℂ (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ) ⟶
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  classical
  let trivial := FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)
  let : Simple trivial := by
    apply (FDRep.simple_iff_isIrreducible _).mpr
    change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
    infer_instance
  have hmaximum := ideal.card_lt hproper
  have hshort : half < n := by omega
  have hiso := full_piece_iso (n := n) (hthree := hthree) half
  rw [length_fiber_card n hthree half] at hiso
  have hcount : (if half = 0 ∨ half = n then 1 else if half < n then 2 else 0) = 2 := by
    simp only [hpositive.ne', hshort.ne, or_self, ite_false, hshort, ite_true]
  rw [hcount] at hiso
  have hclass : (TauCeti.SplitK0.of
      (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      ∑ _ : Fin 2, (1 : ℕ) • TauCeti.SplitK0.of trivial := by
    apply TauCeti.repRingCharacter_injective
    simp only [map_sum, TauCeti.repRingCharacter_of, one_nsmul]
    rw [FDRep.char_iso hiso.some, finiteSum_character]
  have hhom := hom_finrank_of_class trivial
    (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree half)
    (fun _ : Fin 2 => trivial) (fun _ => 1) hclass
  have hbound := hom_embedding_bound trivial
    (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree half)
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half)
    (fullPieceIntertwiner ideal half) (fullPieceMap_injective ideal half hhalf half le_rfl)
  rw [hhom] at hbound
  have hrefl : Nonempty (trivial ≅ trivial) := ⟨Iso.refl trivial⟩
  simpa only [FDRep.finrank_hom_simple_simple, hrefl, ite_true, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hbound

end Schubert.DihedralSplines.HessenbergIdeal.Left
