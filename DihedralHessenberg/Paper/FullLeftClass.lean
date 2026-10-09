import DihedralHessenberg.Paper.LeftFixedRepresentation
import DihedralHessenberg.Paper.SchubertHilbert

/-! # Graded class of the full left quotient -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators

namespace Schubert.DihedralSplines.SchubertSpline
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- Every full left quotient degree is its canonical length count of trivial classes. -/
theorem left_class_coeff (degree : ℕ) :
    PowerSeries.coeff degree (RootSubset.Left.gradedClass (RootSubset.full n) hthree) =
      Nat.card {vertex : DihedralGroup n // length n hthree vertex = degree} •
        (1 : TauCeti.repRing ℂ (DihedralGroup n)) := by
  rw [RootSubset.Left.gradedClass_coeff]
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of, map_nsmul, map_one]
  funext element
  have hcharacter := FDRep.char_iso
    (HessenbergIdeal.Left.full_piece_iso (n := n) (hthree := hthree) degree).some
  rw [finiteSum_character] at hcharacter
  simpa using congrFun hcharacter element

/-- The full left graded representation has exactly the full length polynomial. -/
theorem left_class_polynomial :
    RootSubset.Left.gradedClass (RootSubset.full n) hthree =
      ((HessenbergIdeal.full n hthree).lengthPolynomial.map
        (Nat.castRingHom (TauCeti.repRing ℂ (DihedralGroup n))) :
          PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) := by
  classical
  apply PowerSeries.ext
  intro degree
  rw [left_class_coeff, Polynomial.coeff_coe, Polynomial.coeff_map, HessenbergIdeal.coeff]
  change Nat.card {vertex : DihedralGroup n // length n hthree vertex = degree} •
    (1 : TauCeti.repRing ℂ (DihedralGroup n)) =
      ((Finset.univ.filter fun vertex : DihedralGroup n =>
        (RootSubset.full n).length vertex = degree).card : TauCeti.repRing ℂ (DihedralGroup n))
  simp_rw [RootSubset.length_full n hthree]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- The finite sum places one trivial class at each vertex length. -/
theorem left_class_length_sum :
    RootSubset.Left.gradedClass (RootSubset.full n) hthree =
      ∑ vertex : DihedralGroup n,
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^
          length n hthree vertex := by
  rw [left_class_polynomial, length_sum]
  let morphism : Polynomial ℕ →+* PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
    Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom (Nat.castRingHom (TauCeti.repRing ℂ (DihedralGroup n))))
  change morphism (∑ vertex : DihedralGroup n, Polynomial.X ^ length n hthree vertex) = _
  rw [map_sum]
  simp [morphism]

/-- The full left graded representation is the displayed finite geometric expression. -/
theorem left_class_geometric :
    RootSubset.Left.gradedClass (RootSubset.full n) hthree =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range n,
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent := by
  rw [left_class_polynomial, length_factor]
  let morphism : Polynomial ℕ →+* PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
    Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom (Nat.castRingHom (TauCeti.repRing ℂ (DihedralGroup n))))
  change morphism ((1 + Polynomial.X) *
    ∑ exponent ∈ Finset.range n, Polynomial.X ^ exponent) = _
  rw [map_mul, map_add, map_one, map_sum]
  simp [morphism]

end Schubert.DihedralSplines.SchubertSpline
