import Schubert.DihedralSplines.LeftFixedRepresentation
import Schubert.DihedralSplines.QuotientSymmetry

/-! # Trivial constituent embeddings in every bounded left quotient degree -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- One trivial object at each endpoint and two at each interior degree. -/
def trivialSource (degree : ℕ) : FDRep ℂ (DihedralGroup n) :=
  ⨁ fun _ : Fin (if degree = 0 ∨ degree = ideal.carrier.ncard then 1 else 2) =>
    FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)

omit [NeZero n] in
private theorem source_complement (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    trivialSource ideal (ideal.carrier.ncard - degree) = trivialSource ideal degree := by
  have heq : (ideal.carrier.ncard - degree = 0 ∨
      ideal.carrier.ncard - degree = ideal.carrier.ncard) ↔
        (degree = 0 ∨ degree = ideal.carrier.ncard) := by omega
  have hcount : (if ideal.carrier.ncard - degree = 0 ∨
      ideal.carrier.ncard - degree = ideal.carrier.ncard then 1 else 2 : ℕ) =
        (if degree = 0 ∨ degree = ideal.carrier.ncard then 1 else 2) := by
    simp only [heq]
  exact congrArg (fun count : ℕ => ⨁ fun _ : Fin count =>
    FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) hcount

private theorem lower_embedding (degree : ℕ) (hlower : 2 * degree ≤ ideal.carrier.ncard) :
    ∃ embedding : Representation.IntertwiningMap (trivialSource ideal degree).ρ
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective embedding := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed] at hminimum
  have hmaximum := ideal.indexed.card_le
  rw [← ideal.ncard_indexed] at hmaximum
  have hshort : degree < n := by omega
  have hnotTop : degree ≠ ideal.carrier.ncard := by omega
  have hiso := full_piece_iso (n := n) (hthree := hthree) degree
  have hcount : Nat.card {vertex : DihedralGroup n // length n hthree vertex = degree} =
      (if degree = 0 ∨ degree = ideal.carrier.ncard then 1 else 2) := by
    rw [length_fiber_card n hthree degree]
    simp [hshort.ne, hshort, hnotTop]
  rw [hcount] at hiso
  have hiso' : Nonempty (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree degree ≅
      trivialSource ideal degree) := hiso
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp ⟨hiso'.some.symm⟩
  refine ⟨(fullPieceIntertwiner ideal degree).comp equivalence.toIntertwiningMap, ?_⟩
  exact (fullPieceMap_injective ideal degree hlower degree le_rfl).comp
    equivalence.toLinearEquiv.injective

/-- Every left quotient degree contains its endpoint or doubled trivial constituent. -/
theorem trivialSource_embedding (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    ∃ embedding : Representation.IntertwiningMap (trivialSource ideal degree).ρ
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree),
      Function.Injective embedding := by
  by_cases hlower : 2 * degree ≤ ideal.carrier.ncard
  · exact lower_embedding ideal degree hlower
  · have hexist := lower_embedding ideal (ideal.carrier.ncard - degree) (by omega)
    rw [source_complement ideal degree hdegree] at hexist
    obtain ⟨embedding, hinjective⟩ := hexist
    have hiso := complementary_iso ideal (ideal.carrier.ncard - degree) (by omega)
    rw [show ideal.carrier.ncard - (ideal.carrier.ncard - degree) = degree by omega] at hiso
    obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp hiso
    exact ⟨equivalence.toIntertwiningMap.comp embedding,
      equivalence.toLinearEquiv.injective.comp hinjective⟩

end Schubert.DihedralSplines.HessenbergIdeal.Left
