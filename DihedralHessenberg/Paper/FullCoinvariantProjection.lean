import DihedralHessenberg.Paper.BorelEquivalence
import DihedralHessenberg.Dihedral.TensorCoinvariantAugmentation
import DihedralHessenberg.Paper.CoinvariantSplineMap

/-! The full spline algebra is augmented in its orbit-coordinate factor. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

/-- The full spline algebra is augmented in its orbit-coordinate factor. -/
def fullCoinvariantProjection (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    (RootSubset.full n).Spline →ₐ[ℂ] CoinvariantAlgebra n := by
  letI := (RootSubset.full n).leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial (RootSubset.full n).Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((RootSubset.full n).constantHom hthree).commutes _
  exact ((tensorAugmentation n).comp (borelEquiv n hthree).symm.toAlgHom).restrictScalars ℂ

/-- The projection of a tensor spline augments exactly its second factor. -/
theorem fullCoinvariantProjection_tmul (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (first second : CoordinatePolynomial) :
    fullCoinvariantProjection n hthree
      (borelHom n hthree (first ⊗ₜ[invariantSubalgebra n] second)) =
      Ideal.Quotient.mk (coinvariantIdeal n) first *
        algebraMap ℂ (CoinvariantAlgebra n) second.constantCoeff := by
  let := (RootSubset.full n).leftAlgebra hthree
  change tensorAugmentation n ((borelEquiv n hthree).symm
    (borelEquiv n hthree (first ⊗ₜ[invariantSubalgebra n] second))) = _
  rw [AlgEquiv.symm_apply_apply, tensorAugmentation_tmul]

/-- Constant splines retain their polynomial coinvariant classes. -/
theorem fullCoinvariantProjection_constant (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) :
    fullCoinvariantProjection n hthree ((RootSubset.full n).constantHom hthree polynomial) =
      Ideal.Quotient.mk (coinvariantIdeal n) polynomial := by
  have heq : (RootSubset.full n).constantHom hthree polynomial =
      borelHom n hthree (polynomial ⊗ₜ[invariantSubalgebra n] 1) := by
    apply Subtype.ext
    funext vertex
    simp [borelHom_tmul, RootSubset.constantHom_apply]
  rw [heq, fullCoinvariantProjection_tmul]
  simp

/-- Orbit splines retain only their constant coefficients. -/
theorem fullCoinvariantProjection_orbit (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) :
    fullCoinvariantProjection n hthree ((RootSubset.full n).orbitHom hthree polynomial) =
      algebraMap ℂ (CoinvariantAlgebra n) polynomial.constantCoeff := by
  have heq : (RootSubset.full n).orbitHom hthree polynomial =
      borelHom n hthree (1 ⊗ₜ[invariantSubalgebra n] polynomial) := by
    apply Subtype.ext
    funext vertex
    simp [borelHom_tmul, RootSubset.orbitHom_apply]
  rw [heq, fullCoinvariantProjection_tmul]
  simp

/-- The orbit-coordinate ideal is killed by the full-spline augmentation. -/
theorem fullCoinvariantProjection_ideal (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    RootSubset.Right.ideal (RootSubset.full n) hthree ≤
      RingHom.ker (fullCoinvariantProjection n hthree).toRingHom := by
  rw [RootSubset.Right.ideal_range]
  apply Ideal.span_le.mpr
  rintro value ⟨coordinate, rfl⟩
  change fullCoinvariantProjection n hthree
    ((RootSubset.full n).orbitHom hthree (MvPolynomial.X coordinate)) = 0
  rw [fullCoinvariantProjection_orbit]
  simp

/-- The full right coordinate quotient maps back to coinvariants. -/
def fullCoinvariantInverse (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    RootSubset.Right.Quotient (RootSubset.full n) hthree →ₐ[ℂ] CoinvariantAlgebra n :=
  Ideal.Quotient.liftₐ (RootSubset.Right.ideal (RootSubset.full n) hthree)
    (fullCoinvariantProjection n hthree)
    (fun _ hmem => fullCoinvariantProjection_ideal n hthree hmem)

/-- The factored inverse retains the spline representative's augmentation. -/
theorem fullCoinvariantInverse_map (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (value : (RootSubset.full n).Spline) :
    fullCoinvariantInverse n hthree
      (RootSubset.Right.quotientMap (RootSubset.full n) hthree value) =
        fullCoinvariantProjection n hthree value := rfl

/-- The factored constant map is recovered identically by the full inverse. -/
theorem fullCoinvariantInverse_leftInverse (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Function.LeftInverse (fullCoinvariantInverse n hthree)
      ((RootSubset.full n).coinvariantMap hthree) := by
  intro value
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
  rw [RootSubset.coinvariantMap_mk, fullCoinvariantInverse_map,
    fullCoinvariantProjection_constant]

/-- The coinvariant algebra injects into the full right coordinate quotient. -/
theorem fullCoinvariantMap_injective (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Function.Injective ((RootSubset.full n).coinvariantMap hthree) :=
  (fullCoinvariantInverse_leftInverse n hthree).injective

end Schubert.DihedralSplines
