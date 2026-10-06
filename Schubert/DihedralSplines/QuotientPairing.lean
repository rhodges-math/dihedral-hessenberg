import Schubert.DihedralSplines.FlowupPieceBases
import Schubert.DihedralSplines.PairedProducts
import Schubert.DihedralSplines.QuotientMultiplication
import Schubert.Dihedral.BruhatOrder
import Schubert.Splines.TriangularPairing
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Nondegenerate multiplication of complementary quotient degrees -/

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral Schubert.Splines
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Complementary left quotient multiplication has no left kernel. -/
theorem multiplication_nondegenerate (degree : ℕ)
    (value : RootSubset.Left.piece ideal.toRootSubset hthree degree)
    (hvalue : ∀ partner : RootSubset.Left.piece ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree),
      RootSubset.Left.multiplication ideal.toRootSubset hthree degree
        (ideal.carrier.ncard - degree) value partner = 0) : value = 0 := by
  classical
  let := bruhatPartialOrder n hthree
  let := bruhatPartialOrder_wellFoundedLT n hthree
  apply pairing_left_nondegenerate (pieceBasis ideal degree) (oppositeClass ideal degree)
    (RootSubset.Left.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) _ _ value (fun index => hvalue _)
  · intro first second hnot
    apply Subtype.ext
    rw [RootSubset.Left.multiplication_apply, pieceBasis_apply, oppositeClass_apply]
    change RootSubset.Left.quotientMap ideal.toRootSubset hthree
        (spline ideal first.val) *
        RootSubset.Left.quotientMap ideal.toRootSubset hthree
          (opposite ideal second.val) = 0
    rw [← map_mul, opposite_product_zero ideal first.val second.val hnot, map_zero]
  · intro index heq
    have hproduct := congrArg Subtype.val heq
    rw [RootSubset.Left.multiplication_apply, pieceBasis_apply, oppositeClass_apply] at hproduct
    change RootSubset.Left.quotientMap ideal.toRootSubset hthree
        (spline ideal index.val) *
        RootSubset.Left.quotientMap ideal.toRootSubset hthree
          (opposite ideal index.val) = 0 at hproduct
    rw [← map_mul] at hproduct
    exact paired_product_ne_zero ideal index.val hproduct

/-- The curried complementary multiplication map is injective. -/
theorem multiplication_injective (degree : ℕ) :
    Function.Injective (RootSubset.Left.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) := by
  intro first second heq
  apply sub_eq_zero.mp
  apply multiplication_nondegenerate ideal degree (first - second)
  intro partner
  rw [map_sub, heq, sub_self, LinearMap.zero_apply]

/-- The top quotient piece is one-dimensional. -/
theorem top_finrank :
    Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree ideal.carrier.ncard) = 1 := by
  rw [← HessenbergIdeal.Left.rankPolynomial_coeff, rank_eq, ideal.coeff_top]

/-- Complementary degree pieces have equal dimensions. -/
theorem complementary_finrank (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) =
      Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree)) := by
  rw [← HessenbergIdeal.Left.rankPolynomial_coeff,
    ← HessenbergIdeal.Left.rankPolynomial_coeff, rank_eq]
  exact ideal.coeff_complement degree hdegree

/-- Complementary multiplication is a perfect bilinear pairing. -/
theorem multiplication_bijective (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Function.Bijective (RootSubset.Left.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  have hdimension : Module.finrank ℂ
      (RootSubset.Left.piece ideal.toRootSubset hthree degree) =
      Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree) →ₗ[ℂ]
        RootSubset.Left.piece ideal.toRootSubset hthree
          (degree + (ideal.carrier.ncard - degree))) := by
    rw [Module.finrank_linearMap, Nat.add_sub_of_le hdegree, top_finrank, mul_one]
    exact complementary_finrank ideal degree hdegree
  refine ⟨multiplication_injective ideal degree, ?_⟩
  have hiff := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℂ) (V := RootSubset.Left.piece ideal.toRootSubset hthree degree)
    (V₂ := RootSubset.Left.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree) →ₗ[ℂ]
      RootSubset.Left.piece ideal.toRootSubset hthree (degree + (ideal.carrier.ncard - degree)))
    (f := RootSubset.Left.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) hdimension
  exact hiff.mp (multiplication_injective ideal degree)

/-- Ring multiplication identifies complementary degrees with maps into the top piece. -/
def pairingEquiv (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    RootSubset.Left.piece ideal.toRootSubset hthree degree ≃ₗ[ℂ]
      (RootSubset.Left.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree) →ₗ[ℂ]
        RootSubset.Left.piece ideal.toRootSubset hthree ideal.carrier.ncard) :=
  (LinearEquiv.ofBijective
    (RootSubset.Left.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) (multiplication_bijective ideal degree hdegree)).trans
    (LinearEquiv.congrRight (LinearEquiv.ofEq _ _
      (congrArg (RootSubset.Left.piece ideal.toRootSubset hthree)
        (Nat.add_sub_of_le hdegree))))

/-- The perfect pairing preserves the product of quotient elements. -/
theorem pairingEquiv_apply (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard)
    (first : RootSubset.Left.piece ideal.toRootSubset hthree degree)
    (second : RootSubset.Left.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree)) :
    (pairingEquiv ideal degree hdegree first second :
      RootSubset.Left.Quotient ideal.toRootSubset hthree) = first.val * second.val := rfl


/-- The perfect multiplication pairing is equivariant for diagonal dot translation. -/
theorem pairingEquiv_dot (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard)
    (element : DihedralGroup n)
    (first : RootSubset.Left.piece ideal.toRootSubset hthree degree)
    (second : RootSubset.Left.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree)) :
    (pairingEquiv ideal degree hdegree
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree element first)
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree) element second) :
      RootSubset.Left.Quotient ideal.toRootSubset hthree) =
    RootSubset.Left.dotEquiv ideal.toRootSubset hthree element
      (pairingEquiv ideal degree hdegree first second) := by
  rw [pairingEquiv_apply, pairingEquiv_apply]
  exact ((RootSubset.Left.dotEquiv ideal.toRootSubset hthree element).map_mul
    first.val second.val).symm

end Left
namespace Right
/-- Complementary right quotient multiplication has no left kernel. -/
theorem multiplication_nondegenerate (degree : ℕ)
    (value : RootSubset.Right.piece ideal.toRootSubset hthree degree)
    (hvalue : ∀ partner : RootSubset.Right.piece ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree),
      RootSubset.Right.multiplication ideal.toRootSubset hthree degree
        (ideal.carrier.ncard - degree) value partner = 0) : value = 0 := by
  classical
  let := bruhatPartialOrder n hthree
  let := bruhatPartialOrder_wellFoundedLT n hthree
  apply pairing_left_nondegenerate (pieceBasis ideal degree) (oppositeClass ideal degree)
    (RootSubset.Right.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) _ _ value (fun index => hvalue _)
  · intro first second hnot
    apply Subtype.ext
    rw [RootSubset.Right.multiplication_apply, pieceBasis_apply, oppositeClass_apply]
    change RootSubset.Right.quotientMap ideal.toRootSubset hthree
        (spline ideal first.val) *
        RootSubset.Right.quotientMap ideal.toRootSubset hthree
          (opposite ideal second.val) = 0
    rw [← map_mul, opposite_product_zero ideal first.val second.val hnot, map_zero]
  · intro index heq
    have hproduct := congrArg Subtype.val heq
    rw [RootSubset.Right.multiplication_apply, pieceBasis_apply, oppositeClass_apply] at hproduct
    change RootSubset.Right.quotientMap ideal.toRootSubset hthree
        (spline ideal index.val) *
        RootSubset.Right.quotientMap ideal.toRootSubset hthree
          (opposite ideal index.val) = 0 at hproduct
    rw [← map_mul] at hproduct
    exact paired_product_ne_zero ideal index.val hproduct

/-- The curried complementary multiplication map is injective. -/
theorem multiplication_injective (degree : ℕ) :
    Function.Injective (RootSubset.Right.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) := by
  intro first second heq
  apply sub_eq_zero.mp
  apply multiplication_nondegenerate ideal degree (first - second)
  intro partner
  rw [map_sub, heq, sub_self, LinearMap.zero_apply]

/-- The top quotient piece is one-dimensional. -/
theorem top_finrank :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree
      ideal.carrier.ncard) = 1 := by
  rw [← HessenbergIdeal.Right.rankPolynomial_coeff, rank_eq, ideal.coeff_top]

/-- Complementary degree pieces have equal dimensions. -/
theorem complementary_finrank (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree)) := by
  rw [← HessenbergIdeal.Right.rankPolynomial_coeff,
    ← HessenbergIdeal.Right.rankPolynomial_coeff, rank_eq]
  exact ideal.coeff_complement degree hdegree

/-- Complementary multiplication is a perfect bilinear pairing. -/
theorem multiplication_bijective (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Function.Bijective (RootSubset.Right.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) := by
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  have hdimension : Module.finrank ℂ
      (RootSubset.Right.piece ideal.toRootSubset hthree degree) =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree) →ₗ[ℂ]
        RootSubset.Right.piece ideal.toRootSubset hthree
          (degree + (ideal.carrier.ncard - degree))) := by
    rw [Module.finrank_linearMap, Nat.add_sub_of_le hdegree, top_finrank, mul_one]
    exact complementary_finrank ideal degree hdegree
  refine ⟨multiplication_injective ideal degree, ?_⟩
  have hiff := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℂ) (V := RootSubset.Right.piece ideal.toRootSubset hthree degree)
    (V₂ := RootSubset.Right.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree) →ₗ[ℂ]
      RootSubset.Right.piece ideal.toRootSubset hthree (degree + (ideal.carrier.ncard - degree)))
    (f := RootSubset.Right.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) hdimension
  exact hiff.mp (multiplication_injective ideal degree)

/-- Ring multiplication identifies complementary degrees with maps into the top piece. -/
def pairingEquiv (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    RootSubset.Right.piece ideal.toRootSubset hthree degree ≃ₗ[ℂ]
      (RootSubset.Right.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree) →ₗ[ℂ]
        RootSubset.Right.piece ideal.toRootSubset hthree ideal.carrier.ncard) :=
  (LinearEquiv.ofBijective
    (RootSubset.Right.multiplication ideal.toRootSubset hthree degree
      (ideal.carrier.ncard - degree)) (multiplication_bijective ideal degree hdegree)).trans
    (LinearEquiv.congrRight (LinearEquiv.ofEq _ _
      (congrArg (RootSubset.Right.piece ideal.toRootSubset hthree)
        (Nat.add_sub_of_le hdegree))))

/-- The perfect pairing preserves the product of quotient elements. -/
theorem pairingEquiv_apply (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard)
    (first : RootSubset.Right.piece ideal.toRootSubset hthree degree)
    (second : RootSubset.Right.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree)) :
    (pairingEquiv ideal degree hdegree first second :
      RootSubset.Right.Quotient ideal.toRootSubset hthree) = first.val * second.val := rfl


/-- The perfect multiplication pairing is equivariant for diagonal dot translation. -/
theorem pairingEquiv_dot (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard)
    (element : DihedralGroup n)
    (first : RootSubset.Right.piece ideal.toRootSubset hthree degree)
    (second : RootSubset.Right.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree)) :
    (pairingEquiv ideal degree hdegree
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree element first)
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree) element second) :
      RootSubset.Right.Quotient ideal.toRootSubset hthree) =
    RootSubset.Right.dotEquiv ideal.toRootSubset hthree element
      (pairingEquiv ideal degree hdegree first second) := by
  rw [pairingEquiv_apply, pairingEquiv_apply]
  exact ((RootSubset.Right.dotEquiv ideal.toRootSubset hthree element).map_mul
    first.val second.val).symm

end Right
end Schubert.DihedralSplines.FlowupSpline
