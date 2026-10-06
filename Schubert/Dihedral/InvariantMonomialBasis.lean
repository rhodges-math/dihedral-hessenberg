import Mathlib.RingTheory.MvPolynomial.Basic
import Schubert.Dihedral.InvariantPolynomialRing
import Schubert.Dihedral.InvariantDegrees

/-! # Explicit monomial bases of the invariant algebra

The polynomial-ring equivalence evaluates at the two invariant generators. Consequently
its monomial basis consists of their pure products, with their polynomial degrees.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The invariant polynomial-ring equivalence evaluates at the two basic generators. -/
theorem exists_invariantPolynomialEquiv_aeval (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ equivalence : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] invariantSubalgebra n,
      ∀ polynomial, (equivalence polynomial : CoordinatePolynomial) =
        MvPolynomial.aeval (fun coordinate : Fin 2 =>
          if coordinate = 0 then quadraticInvariant else higherInvariant n) polynomial := by
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
  refine ⟨(basicInvariants_algebraicIndependent n (by omega)).aevalEquiv.trans
    (Subalgebra.equivOfEq _ _ hadjoin), fun polynomial => ?_⟩
  rfl

/-- Products of basic invariant powers form a complex basis of the invariant algebra. -/
theorem exists_invariant_monomial_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis (Fin 2 →₀ ℕ) ℂ (invariantSubalgebra n),
      ∀ exponent, (basis exponent : CoordinatePolynomial) =
        quadraticInvariant ^ exponent 0 * higherInvariant n ^ exponent 1 := by
  classical
  obtain ⟨equivalence, hequivalence⟩ := exists_invariantPolynomialEquiv_aeval n hthree
  refine ⟨(MvPolynomial.basisMonomials (Fin 2) ℂ).map equivalence.toLinearEquiv,
    fun exponent => ?_⟩
  rw [Module.Basis.map_apply]
  change (equivalence (MvPolynomial.monomial exponent 1) : CoordinatePolynomial) = _
  rw [hequivalence, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_two]

/-- Each invariant monomial has its weighted generator degree. -/
theorem invariant_monomial_isHomogeneous (n : ℕ) (exponent : Fin 2 →₀ ℕ) :
    (quadraticInvariant ^ exponent 0 * higherInvariant n ^ exponent 1).IsHomogeneous
      (2 * exponent 0 + n * exponent 1) := by
  exact (quadraticInvariant_isHomogeneous.pow (exponent 0)).mul
    ((higherInvariant_isHomogeneous n).pow (exponent 1))

end Schubert.Dihedral
