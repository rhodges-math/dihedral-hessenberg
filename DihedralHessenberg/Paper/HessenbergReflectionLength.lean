import DihedralHessenberg.Paper.HessenbergClassification
import DihedralHessenberg.Dihedral.ConjugatedLength

/-! # Membership bounds from the lengths of indexed root reflections -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Every root in an ideal has reflection length at most the ideal's cardinality. -/
theorem reflection_length_le_card_of_mem (ideal : HessenbergSpace n hthree)
    (index : PositiveRootIndex n) (hmember : index ∈ ideal.roots) :
    Schubert.Dihedral.length n hthree (rootReflection index) ≤ ideal.roots.card := by
  rw [length_rootReflection]
  rcases ideal.root_membership_classification with hprefix | ⟨hodd, _, hother⟩
  · have hindex := (hprefix index).mp hmember
    omega
  · have hindex := (hother index).mp hmember
    have hmod := Nat.odd_iff.mp hodd
    omega

/-- Every root with strictly shorter reflection length than the ideal size belongs to it. -/
theorem mem_roots_of_reflection_length_lt_card (ideal : HessenbergSpace n hthree)
    (index : PositiveRootIndex n)
    (hshort : Schubert.Dihedral.length n hthree (rootReflection index) < ideal.roots.card) :
    index ∈ ideal.roots := by
  rw [length_rootReflection] at hshort
  rcases ideal.root_membership_classification with hprefix | ⟨hodd, _, hother⟩
  · apply (hprefix index).mpr
    omega
  · apply (hother index).mpr
    have hmod := Nat.odd_iff.mp hodd
    exact Or.inl (by omega)

/-- For an even-sized ideal, root membership is exactly the strict reflection-length bound. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.roots_iff_reflection_length_even (ideal :
  HessenbergSpace n hthree)
    (heven : Even ideal.roots.card) (index : PositiveRootIndex n) :
    index ∈ ideal.roots ↔
      Schubert.Dihedral.length n hthree (rootReflection index) < ideal.roots.card := by
  constructor
  · intro hmember
    have hbound := ideal.reflection_length_le_card_of_mem index hmember
    rw [length_rootReflection] at hbound ⊢
    have hmod := Nat.even_iff.mp heven
    omega
  · exact ideal.mem_roots_of_reflection_length_lt_card index

/-- In an even-sized ideal, a simple edge is characterized by the length of its conjugate. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.simple_edge_iff_length_lt_even (ideal :
  HessenbergSpace n hthree)
    (heven : Even ideal.roots.card) (simple : Fin 2) (element : DihedralGroup n) :
    (∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) ↔
        Schubert.Dihedral.length n hthree
          (element⁻¹ * simpleReflection n simple * element) < ideal.roots.card := by
  constructor
  · rintro ⟨index, hmember, hneighbor⟩
    have heq : rootReflection index = element⁻¹ * simpleReflection n simple * element := by
      have hcancel := congrArg (fun value => element⁻¹ * value) hneighbor
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hcancel.symm
    rw [← heq]
    exact (ideal.roots_iff_reflection_length_even heven index).mp hmember
  · intro hshort
    have hreflection := ((coxeterSystem n hthree).isReflection_simple simple).conj element⁻¹
    rw [coxeterSystem_simple, inv_inv] at hreflection
    obtain ⟨index, hindex⟩ :=
      (isReflection_iff_exists_rootReflection n hthree _).mp hreflection
    refine ⟨index, ?_, ?_⟩
    · apply (ideal.roots_iff_reflection_length_even heven index).mpr
      rw [hindex]
      exact hshort
    · rw [hindex]
      group

/-- An even-sized ideal has simple ascent edges exactly in its two outer length ranges. -/
theorem simple_ascent_edge_iff_of_even (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hcard : ideal.roots.card = 2 * half)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1) :
    (∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) ↔
        Schubert.Dihedral.length n hthree element < half ∨
          n - half ≤ Schubert.Dihedral.length n hthree element := by
  have heven : Even ideal.roots.card := ⟨half, by omega⟩
  have hbound := length_le_polygon_parameter n hthree element
  have hsizeBound := ideal.card_le
  have hminimum := ideal.two_le_card
  rw [ideal.simple_edge_iff_length_lt_even heven,
    _root_.Schubert.Dihedral.Reflections.Lengths.conjugate_ascent_min n hthree simple element
      hascent, hcard,
    min_lt_iff]
  omega

/-- An even-sized ideal has simple descent edges exactly in its two outer length ranges. -/
theorem simple_descent_edge_iff_of_even (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hcard : ideal.roots.card = 2 * half)
    (simple : Fin 2) (element : DihedralGroup n)
    (hdescent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) + 1 =
      Schubert.Dihedral.length n hthree element) :
    (∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) ↔
        Schubert.Dihedral.length n hthree element ≤ half ∨
          n - half < Schubert.Dihedral.length n hthree element := by
  have heven : Even ideal.roots.card := ⟨half, by omega⟩
  have hbound := length_le_polygon_parameter n hthree element
  have hsizeBound := ideal.card_le
  have hminimum := ideal.two_le_card
  rw [ideal.simple_edge_iff_length_lt_even heven,
    length_conjugate_simple_of_left_descent n hthree simple element hdescent, hcard]
  split_ifs <;> omega

end Schubert.DihedralSplines.HessenbergSpace
