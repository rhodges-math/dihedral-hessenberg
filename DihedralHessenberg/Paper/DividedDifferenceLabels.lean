import DihedralHessenberg.Dihedral.RootPolynomialAction
import DihedralHessenberg.Dihedral.RootPreservation
import DihedralHessenberg.Dihedral.RootSignedConjugation
import DihedralHessenberg.Dihedral.ReflectionIndex
import Mathlib.Algebra.Ring.Associated

/-! # Signed linear labels under the dihedral action -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Every root image is a positive indexed root or its negative. -/
theorem exists_signed_root_image (n : ℕ) [NeZero n] (vertex : DihedralGroup n)
    (index : PositiveRootIndex n) :
    ∃ image : PositiveRootIndex n,
      vectorOperator n vertex (complexPositiveRoot n index) = complexPositiveRoot n image ∨
        vectorOperator n vertex (complexPositiveRoot n index) = -complexPositiveRoot n image := by
  obtain ⟨vector, hvector, himage⟩ := vectorOperator_complexify_mem_roots n vertex
    (positiveRoot n index) (Or.inl ⟨index, rfl⟩)
  change vectorOperator n vertex (complexPositiveRoot n index) = complexify vector at himage
  rcases hvector with hpositive | hnegative
  · obtain ⟨image, rfl⟩ := hpositive
    exact ⟨image, Or.inl himage⟩
  · obtain ⟨image, hnegative⟩ := hnegative
    have heq : vector = -positiveRoot n image := by rw [hnegative, neg_neg]
    refine ⟨image, Or.inr ?_⟩
    rw [himage, heq]
    funext coordinate
    simp [complexify, complexPositiveRoot]

/-- Every action-transformed root polynomial is an indexed root polynomial up to sign. -/
theorem exists_signed_root_polynomial (n : ℕ) [NeZero n] (vertex : DihedralGroup n)
    (index : PositiveRootIndex n) :
    ∃ image : PositiveRootIndex n,
      polynomialAction n vertex (rootPolynomial n index) = rootPolynomial n image ∨
        polynomialAction n vertex (rootPolynomial n index) = -rootPolynomial n image := by
  obtain ⟨image, himage | himage⟩ := exists_signed_root_image n vertex index
  · refine ⟨image, Or.inl ?_⟩
    change polynomialAction n vertex (linearPolynomial (complexPositiveRoot n index)) =
      linearPolynomial (complexPositiveRoot n image)
    rw [polynomialAction_linearPolynomial, himage]
  · refine ⟨image, Or.inr ?_⟩
    rw [rootPolynomial, polynomialAction_linearPolynomial, himage]
    simp [linearPolynomial, rootPolynomial, add_comm]

/-- An edge label is transverse to a root label or is its parallel reflection edge. -/
theorem rootPolynomial_edge_dichotomy (n : ℕ) [NeZero n] (vertex : DihedralGroup n)
    (edgeIndex index : PositiveRootIndex n) :
    IsRelPrime (polynomialAction n vertex (rootPolynomial n edgeIndex))
        (rootPolynomial n index) ∨
      (Associated (polynomialAction n vertex (rootPolynomial n edgeIndex))
          (rootPolynomial n index) ∧
        vertex * rootReflection edgeIndex = rootReflection index * vertex) := by
  obtain ⟨image, himage⟩ := exists_signed_root_image n vertex edgeIndex
  have hpolynomial : polynomialAction n vertex (rootPolynomial n edgeIndex) =
      rootPolynomial n image ∨
        polynomialAction n vertex (rootPolynomial n edgeIndex) = -rootPolynomial n image := by
    rcases himage with hpositive | hnegative
    · left
      change polynomialAction n vertex (linearPolynomial (complexPositiveRoot n edgeIndex)) =
        linearPolynomial (complexPositiveRoot n image)
      rw [polynomialAction_linearPolynomial, hpositive]
    · right
      rw [rootPolynomial, polynomialAction_linearPolynomial, hnegative]
      simp [linearPolynomial, rootPolynomial, add_comm]
  by_cases heq : image = index
  · subst image
    right
    refine ⟨?_, rootReflection_endpoint_of_signed_image n vertex edgeIndex index himage⟩
    rcases hpolynomial with hpositive | hnegative
    · rw [hpositive]
    · rw [hnegative]
      exact (Associated.refl _).neg_left
  · left
    have hprime := rootPolynomial_isRelPrime n image index heq
    rcases hpolynomial with hpositive | hnegative
    · rw [hpositive]
      exact hprime
    · rw [hnegative]
      simpa only [IsRelPrime, dvd_neg] using hprime

/-- A left reflection endpoint forces the corresponding edge-label principal ideal. -/
theorem _root_.Schubert.DihedralSplines.IndexedDD.associated_of_endpoint (n : ℕ) [NeZero n]
    (vertex : DihedralGroup n) (edgeIndex index : PositiveRootIndex n)
    (hendpoint : vertex * rootReflection edgeIndex = rootReflection index * vertex) :
    Associated (polynomialAction n vertex (rootPolynomial n edgeIndex))
      (rootPolynomial n index) := by
  obtain ⟨image, himage⟩ := exists_signed_root_image n vertex edgeIndex
  have hother := rootReflection_endpoint_of_signed_image n vertex edgeIndex image himage
  have hindex : image = index :=
    rootReflection_injective n (mul_right_cancel (hother.symm.trans hendpoint))
  subst image
  rcases himage with hpositive | hnegative
  · have hpolynomial : polynomialAction n vertex (rootPolynomial n edgeIndex) =
        rootPolynomial n index := by
      change polynomialAction n vertex (linearPolynomial (complexPositiveRoot n edgeIndex)) =
        linearPolynomial (complexPositiveRoot n index)
      rw [polynomialAction_linearPolynomial, hpositive]
    rw [hpolynomial]
  · have hpolynomial : polynomialAction n vertex (rootPolynomial n edgeIndex) =
        -rootPolynomial n index := by
      rw [rootPolynomial, polynomialAction_linearPolynomial, hnegative]
      simp [linearPolynomial, rootPolynomial, add_comm]
    rw [hpolynomial]
    exact (Associated.refl _).neg_left

end Schubert.DihedralSplines
