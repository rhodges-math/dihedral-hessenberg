import Schubert.Dihedral.InvariantAction
import Schubert.Dihedral.InvariantFreeness
import Schubert.Splines.OrbitBasisIndependent

/-! An invariant-module basis has independent polynomial orbit columns. -/

noncomputable section
namespace Schubert.Dihedral

/-- An invariant-module basis has independent polynomial orbit columns. -/
theorem exists_invariant_orbit_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis (DihedralGroup n) (invariantSubalgebra n) CoordinatePolynomial,
      LinearIndependent CoordinatePolynomial
        (fun index => fun element => polynomialAction n element (basis index)) := by
  classical
  obtain ⟨basis, _⟩ := exists_invariant_axial_basis n hthree
  let equivalence : (Fin n × Fin 2) ≃ DihedralGroup n := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, DihedralGroup.card]
    omega)
  refine ⟨basis.reindex equivalence, ?_⟩
  exact Schubert.Splines.orbit_basis_independent (basis.reindex equivalence)
    (invariantAction n) (invariantAction_injective n)

end Schubert.Dihedral
