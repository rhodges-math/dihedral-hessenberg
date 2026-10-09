import DihedralHessenberg.Paper.PaperSpline
import DihedralHessenberg.Paper.TriangleCayley
import DihedralHessenberg.Paper.SquareCayley

/-! # Exact finite edge tables for spline diagrams -/

noncomputable section
namespace Schubert.Dihedral.RootSubset
open Schubert.DihedralSplines

/-- Complete oriented representatives and their exact labels test the spline condition. -/
theorem isSpline_iff_table {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)
    {I : Type*} (pairs : I → DihedralGroup n × DihedralGroup n)
    (hmem : ∀ row, pairs row ∈ selected.edges) (labels : I → CoordinatePolynomial)
    (hlabels : ∀ row, selected.edgeLabel ⟨pairs row, hmem row⟩ = labels row)
    (hcover : ∀ pair, pair ∈ selected.edges ↔
      ∃ row, pair = pairs row ∨ pair = (pairs row).swap)
    (value : DihedralGroup n → CoordinatePolynomial) :
    selected.IsSpline value ↔ ∀ row, labels row ∣
      value (pairs row).1 - value (pairs row).2 := by
  rw [selected.isSpline_iff_graph]
  constructor
  · intro hvalue row
    have hrow := hvalue ⟨pairs row, hmem row⟩
    change selected.edgeLabel ⟨pairs row, hmem row⟩ ∣
      value (pairs row).1 - value (pairs row).2 at hrow
    rwa [hlabels] at hrow
  · intro hvalue edge
    obtain ⟨row, hrow | hrow⟩ := (hcover edge.val).mp edge.property
    · have hedge : edge = ⟨pairs row, hmem row⟩ := Subtype.ext hrow
      change selected.edgeLabel edge ∣ value edge.val.1 - value edge.val.2
      rw [hedge, hlabels]
      exact hvalue row
    · have hedge : edge = selected.reverse ⟨pairs row, hmem row⟩ := Subtype.ext hrow
      change selected.edgeLabel edge ∣ value edge.val.1 - value edge.val.2
      rw [hedge, selected.label_reverse hthree, hlabels]
      change -labels row ∣ value (pairs row).2 - value (pairs row).1
      simpa only [neg_dvd, dvd_neg, neg_sub] using (hvalue row).neg_right

end Schubert.Dihedral.RootSubset
