import DihedralHessenberg.Paper.DominanceMiddle
import DihedralHessenberg.Dihedral.UpperBlock
import DihedralHessenberg.Dihedral.BlockOrbits

/-! # Upper supports of dominance witnesses -/

noncomputable section

open scoped Classical Pointwise

namespace Schubert.DihedralSplines.HessenbergIdeal.MiddleWitness

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} {ideal : HessenbergIdeal n hthree}
variable {half size : ℕ} {alpha : PositiveRoot n}

private theorem reverse_pair (witness : MiddleWitness ideal half alpha size) :
    (witness.beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
      (witness.beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
  rcases witness.pair with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

/-- Reversal of the alternating expression identifies the right ascending simple vector. -/
theorem right_ascent (witness : MiddleWitness ideal half alpha size) (hshort : size < n) :
    length n hthree (witness.vertex *
      (if Even size then witness.beta else alpha).reflection) = size + 1 := by
  classical
  by_cases heven : Even size
  · rw [ite_eq_left heven, ← length_inv n hthree (_ * _), mul_inv_rev,
      PositiveRoot.reflection_inv, witness.word, PositiveRoot.alternating_inv,
      ite_eq_left heven]
    exact PositiveRoot.alternating_ascent witness.beta alpha witness.reverse_pair size (by omega)
  · rw [ite_eq_right heven, ← length_inv n hthree (_ * _), mul_inv_rev,
      PositiveRoot.reflection_inv, witness.word, PositiveRoot.alternating_inv,
      ite_eq_right heven]
    exact PositiveRoot.alternating_ascent alpha witness.beta witness.pair size (by omega)

/-- The high witness's upper ideal is its alternating block in the right orientation. -/
theorem upper_block (witness : MiddleWitness ideal half alpha size) (hshort : size < n)
    (hhigh : n < 2 * size + 1) :
    {target | BruhatLE n hthree witness.vertex target} =
      (alternatingBlock witness.vertex (if Even size then witness.beta else alpha)
        (if Even size then alpha else witness.beta) (n - size - 1) : Set (DihedralGroup n)) := by
  classical
  have hright : length n hthree (witness.vertex *
      (if Even size then witness.beta else alpha).reflection) =
      length n hthree witness.vertex + 1 := by
    simpa only [witness.canonical] using witness.right_ascent hshort
  by_cases heven : Even size
  · simp only [ite_eq_left heven] at hright ⊢
    simpa only [witness.canonical] using
      (alternatingBlock_upper witness.vertex witness.beta alpha witness.reverse_pair hright
        (by rw [witness.canonical]; exact hhigh)).symm
  · simp only [ite_eq_right heven] at hright ⊢
    simpa only [witness.canonical] using
      (alternatingBlock_upper witness.vertex alpha witness.beta witness.pair hright
        (by rw [witness.canonical]; exact hhigh)).symm

/-- The upper support orbit is the standard orbit of its right-oriented block. -/
theorem upper_orbit [NeZero n] (witness : MiddleWitness ideal half alpha size) (hshort : size < n)
    (hhigh : n < 2 * size + 1) :
    MulAction.orbit (DihedralGroup n)
      (Finset.univ.filter fun target => BruhatLE n hthree witness.vertex target) =
    MulAction.orbit (DihedralGroup n)
      (alternatingBlock 1 (if Even size then witness.beta else alpha)
        (if Even size then alpha else witness.beta) (n - size - 1)) := by
  classical
  rw [MulAction.orbit_eq_iff, alternatingBlock_orbit]
  refine ⟨witness.vertex, ?_⟩
  apply Finset.coe_injective
  simpa only [Finset.coe_filter, Finset.mem_univ, true_and] using
    witness.upper_block hshort hhigh

/-- The even middle witness is nonterminal, high, and has a proper short-reflection bound. -/
theorem even_bounds (witness : MiddleWitness ideal half alpha (n - half))
    (hcard : ideal.carrier.ncard = 2 * half) (hproper : ideal.carrier ≠ positiveRoots n) :
    length n hthree witness.vertex < n ∧
      n < 2 * length n hthree witness.vertex + 1 ∧
      2 * (n - length n hthree witness.vertex - 1) + 1 < n := by
  have hmaximum := ideal.card_lt hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  rw [hcard] at hmaximum
  rw [witness.canonical]
  omega

/-- All short-reflection roots of an even middle upper support are selected. -/
theorem even_selected (witness : MiddleWitness ideal half alpha (n - half))
    (hcard : ideal.carrier.ncard = 2 * half) (hproper : ideal.carrier ≠ positiveRoots n)
    (gamma : PositiveRoot n)
    (hshort : length n hthree gamma.reflection ≤
      2 * (n - length n hthree witness.vertex - 1) + 1) : gamma.val ∈ ideal := by
  have hmaximum := ideal.card_lt hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  rw [hcard] at hmaximum
  rw [witness.canonical] at hshort
  apply ideal.selected_of_short
  rw [hcard]
  omega

/-- The odd middle witness has exactly the terminal-selected upper-block cardinality. -/
theorem odd_card (witness : MiddleWitness ideal half alpha (n - half - 1))
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    ideal.carrier.ncard = 2 * (n - length n hthree witness.vertex - 1) + 1 := by
  have hmaximum := ideal.card_lt hproper
  rw [hcard] at hmaximum
  rw [witness.canonical, hcard]
  omega

/-- The odd middle witness is nonterminal, high, and its terminal reflection is proper. -/
theorem odd_bounds (witness : MiddleWitness ideal half alpha (n - half - 1))
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    length n hthree witness.vertex < n ∧
      n < 2 * length n hthree witness.vertex + 1 ∧
      2 * (n - length n hthree witness.vertex - 1) + 1 < n := by
  have hmaximum := ideal.card_lt hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  rw [hcard] at hmaximum
  rw [witness.canonical]
  omega

end Schubert.DihedralSplines.HessenbergIdeal.MiddleWitness

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The upper supports of the two even middle witnesses have disjoint translation orbits. -/
theorem middle_even_disjoint [NeZero n] (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    Disjoint
      (MulAction.orbit (DihedralGroup n)
        (Finset.univ.filter fun target => BruhatLE n hthree first.vertex target))
      (MulAction.orbit (DihedralGroup n)
        (Finset.univ.filter fun target => BruhatLE n hthree second.vertex target)) := by
  classical
  have hmaximum := ideal.card_lt hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  rw [hcard] at hmaximum
  have hfirst : first.beta = simpleRoot n hthree 1 := by
    rcases first.pair with h | h
    · exact h.2
    · exact False.elim (simpleRoot_ne n hthree h.1)
  have hsecond : second.beta = simpleRoot n hthree 0 := by
    rcases second.pair with h | h
    · exact False.elim ((simpleRoot_ne n hthree).symm h.1)
    · exact h.2
  have hdepth : n - (n - half) - 1 = half - 1 := by omega
  rw [first.upper_orbit (by omega) (by omega), second.upper_orbit (by omega) (by omega),
    hfirst, hsecond, hdepth]
  have hdisjoint := block_orbits_disjoint (hthree := hthree) (half - 1) (by omega)
  split_ifs
  · exact hdisjoint.symm
  · exact hdisjoint

end Schubert.DihedralSplines.HessenbergIdeal
