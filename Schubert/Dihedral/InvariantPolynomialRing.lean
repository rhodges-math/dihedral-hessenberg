import Schubert.Dihedral.BasicInvariantIndependence

/-! # The dihedral invariant algebra is a polynomial algebra

Generation and algebraic independence identify the existing invariant subalgebra
with a polynomial algebra on two generators.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The official invariant subalgebra is isomorphic to a polynomial algebra on two variables. -/
theorem nonempty_invariantPolynomialEquiv (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Nonempty (MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] invariantSubalgebra n) := by
  have hrange : Set.range (fun coordinate : Fin 2 =>
      if coordinate = 0 then quadraticInvariant else higherInvariant n) =
      ({quadraticInvariant, higherInvariant n} : Set CoordinatePolynomial) := by
    ext polynomial
    constructor
    · rintro ⟨coordinate, rfl⟩
      fin_cases coordinate <;> simp
    · intro hpolynomial
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpolynomial
      rcases hpolynomial with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hadjoin : Algebra.adjoin ℂ (Set.range (fun coordinate : Fin 2 =>
      if coordinate = 0 then quadraticInvariant else higherInvariant n)) =
      invariantSubalgebra n := by
    rw [hrange, ← _root_.Schubert.Dihedral.Invariants.eq_generator_adjoin n hthree]
  exact ⟨(basicInvariants_algebraicIndependent n (by omega)).aevalEquiv.trans
    (Subalgebra.equivOfEq _ _ hadjoin)⟩

end Schubert.Dihedral
