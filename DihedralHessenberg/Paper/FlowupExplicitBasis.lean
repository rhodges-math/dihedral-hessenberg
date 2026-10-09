import DihedralHessenberg.Paper.FlowupBoundary

/-! # Homogeneous bases with explicit geometric boundary formulas -/

noncomputable section

namespace Schubert.DihedralSplines.FlowupSpline

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Both polynomial bases share the homogeneous splines and displayed formulas. -/
theorem basis_explicit :
    ∃ values : DihedralGroup n → ideal.toRootSubset.Spline,
      (∀ vertex, values vertex = spline ideal vertex) ∧
      (letI := ideal.toRootSubset.leftAlgebra hthree;
        ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline,
          ∀ vertex, vectors vertex = values vertex) ∧
      (letI := ideal.toRootSubset.rightAlgebra hthree;
        ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline,
          ∀ vertex, vectors vertex = values vertex) ∧
      ∀ vertex, values vertex ∈ ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) ∧
        ideal.toRootSubset.degree (values vertex) = ideal.toRootSubset.length vertex ∧
        (values vertex = ideal.toRootSubset.restrictFull (SchubertSpline.spline n hthree vertex) ∨
          Nonempty (BoundaryForm ideal vertex (values vertex))) := by
  refine ⟨spline ideal, (fun _ => rfl), ?_, ?_, ?_⟩
  · let := ideal.toRootSubset.leftAlgebra hthree
    exact ⟨Left.basis ideal, Left.basis_apply ideal⟩
  · let := ideal.toRootSubset.rightAlgebra hthree
    exact ⟨Right.basis ideal, Right.basis_apply ideal⟩
  · intro vertex
    exact ⟨homogeneous ideal vertex, degree ideal vertex, shape ideal vertex⟩

end Schubert.DihedralSplines.FlowupSpline
