import DihedralHessenberg.Paper.DominanceOddWitness
import DihedralHessenberg.Paper.OddTerminal
import DihedralHessenberg.Dihedral.TerminalConjugate

/-! # Dominance of the selected terminal vector -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem dominant_of_terminal (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha beta gamma : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hselected : gamma.val ∈ ideal)
    (hconjugate : gamma.reflection =
      (beta.alternatingProduct alpha (n - half - 1))⁻¹ * alpha.reflection *
        beta.alternatingProduct alpha (n - half - 1)) : ideal.IsDominant alpha := by
  let element := beta.alternatingProduct alpha (n - half - 1)
  change gamma.reflection = element⁻¹ * alpha.reflection * element at hconjugate
  have hmaximum := ideal.card_lt hproper
  rw [hcard] at hmaximum
  have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
      (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
    rcases hpair with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  have halphaSimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1 :=
    hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hbetaSimple : beta = simpleRoot n hthree 0 ∨ beta = simpleRoot n hthree 1 :=
    hpair.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hneRoots : alpha ≠ beta := by
    rcases hpair with h | h
    · simpa only [h.1, h.2] using simpleRoot_ne n hthree
    · simpa only [h.1, h.2] using (simpleRoot_ne n hthree).symm
  have hlength : length n hthree element = n - half - 1 :=
    PositiveRoot.alternating_length beta alpha hreverse _ (by omega)
  have hascent : length n hthree (alpha.reflection * element) = n - half := by
    have := PositiveRoot.alternating_ascent alpha beta hpair (n - half - 1) (by omega)
    change length n hthree (alpha.reflection * element) = _ at this
    omega
  have hdescent : length n hthree (beta.reflection * element) + 1 = n - half - 1 :=
    PositiveRoot.alternating_descent alpha beta hpair _ (by omega) (by omega)
  have hup : BruhatLE n hthree element (alpha.reflection * element) :=
    bruhatLE_of_length_lt n hthree (by omega)
  have hne : element ≠ alpha.reflection * element := by
    intro heq
    have := congrArg (length n hthree) heq
    omega
  have hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges :=
    (ideal.toRootSubset.edge_iff_conjugate alpha gamma element hconjugate).mpr hselected
  have hneighbor : alpha.reflection * element = element * gamma.reflection := by
    rw [hconjugate]
    group
  have hgammaLength : length n hthree gamma.reflection = ideal.carrier.ncard := by
    rw [alpha.ascent_length hthree gamma halphaSimple element hup hne hneighbor, hlength,
      ite_eq_right (by omega), hcard]
    omega
  have hnot : (element, beta.reflection * element) ∉ ideal.toRootSubset.edges := by
    intro hselectedEdge
    obtain ⟨delta, hdeltaSelected, hdeltaNeighbor⟩ :=
      (ideal.toRootSubset.mem_edges _).mp hselectedEdge
    change beta.reflection * element = element * delta.reflection at hdeltaNeighbor
    have hdeltaLength := beta.descent_length hthree delta hbetaSimple element
      (bruhatLE_of_length_lt n hthree (by omega))
      (by intro heq; have := congrArg (length n hthree) heq; omega) hdeltaNeighbor
    rw [hlength] at hdeltaLength
    have hdeltaLower : ideal.carrier.ncard ≤ length n hthree delta.reflection := by
      rw [hdeltaLength, hcard]
      split_ifs <;> omega
    have hdeltaUpper := ideal.reflection_length_le delta hdeltaSelected
    have heq := ideal.terminal_unique half hcard gamma delta hselected hdeltaSelected
      hgammaLength (by omega)
    apply hneRoots
    apply PositiveRoot.reflection_injective n
    have hneighborEq : alpha.reflection * element = beta.reflection * element := by
      rw [hneighbor, hdeltaNeighbor, heq]
    exact mul_right_cancel hneighborEq
  have hhalfCard : 2 * half ≤ ideal.indexed.roots.card := by
    rw [← ideal.ncard_indexed, hcard]
    omega
  have hnextDegree : ideal.toRootSubset.length (alpha.reflection * element) = half + 1 := by
    have hupper := HessenbergSpace.LengthRanges.card_sub_complementary ideal.indexed half
      hhalfCard (alpha.reflection * element) (by omega)
    rw [← ideal.length_indexed, ← ideal.ncard_indexed, hascent, hcard] at hupper
    omega
  have hstep := ideal.length_edge alpha halphaSimple element hup hne hedge
  rw [hnextDegree] at hstep
  refine ⟨beta, hpair, n - half - 1, by omega, by omega, ?_⟩
  change ideal.toRootSubset.length element = ideal.carrier.ncard / 2 ∧
    (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ∧
      (element, beta.reflection * element) ∉ ideal.toRootSubset.edges
  rw [hcard]
  exact ⟨by omega, hedge, hnot⟩

private theorem dominant_iff_terminal (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha beta gamma : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hconjugate : gamma.reflection =
      (beta.alternatingProduct alpha (n - half - 1))⁻¹ * alpha.reflection *
        beta.alternatingProduct alpha (n - half - 1)) :
    ideal.IsDominant alpha ↔ gamma.val ∈ ideal := by
  constructor
  · intro hdominant
    obtain ⟨other, hotherPair, hconditions⟩ :=
      ideal.dominant_odd_witness half hcard hproper alpha hdominant
    obtain ⟨first, hfirstAlpha, hfirstBeta⟩ := simple_pair_index alpha beta hpair
    obtain ⟨second, hsecondAlpha, hsecondOther⟩ := simple_pair_index alpha other hotherPair
    have heq : first = second := simpleRoot_injective n hthree
      (hfirstAlpha.symm.trans hsecondAlpha)
    have hother : other = beta := hsecondOther.trans (by rw [← heq]; exact hfirstBeta.symm)
    rw [hother] at hconditions
    exact (ideal.toRootSubset.edge_iff_conjugate alpha gamma
      (beta.alternatingProduct alpha (n - half - 1)) hconjugate).mp hconditions.2.1
  · exact fun hselected =>
      dominant_of_terminal ideal half hcard hproper alpha beta gamma hpair hselected hconjugate

/-- The first simple vector is dominant exactly for its parity-prescribed selected terminal. -/
theorem dominant_first_iff (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    ideal.IsDominant (simpleRoot n hthree 0) ↔
      if Even (n - half - 1) then
        (positiveRootEquiv n ⟨2 * half + 1, by have := ideal.card_lt hproper; omega⟩).val ∈ ideal
      else
        (positiveRootEquiv n ⟨2 * half, by have := ideal.card_lt hproper; omega⟩).val ∈ ideal := by
  classical
  have hbound : 2 * half + 1 < n := by have := ideal.card_lt hproper; omega
  have hconjugate := first_terminal_conjugate n hthree half hbound
  dsimp only at hconjugate
  split_ifs at hconjugate ⊢ with heven
  · exact dominant_iff_terminal ideal half hcard hproper _ _ _ (Or.inl ⟨rfl, rfl⟩)
      hconjugate.symm
  · exact dominant_iff_terminal ideal half hcard hproper _ _ _ (Or.inl ⟨rfl, rfl⟩)
      hconjugate.symm

/-- The second simple vector is dominant exactly for the opposite selected terminal. -/
theorem dominant_second_iff (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    ideal.IsDominant (simpleRoot n hthree 1) ↔
      if Even (n - half - 1) then
        (positiveRootEquiv n ⟨2 * half, by have := ideal.card_lt hproper; omega⟩).val ∈ ideal
      else
        (positiveRootEquiv n ⟨2 * half + 1, by have := ideal.card_lt hproper; omega⟩).val ∈ ideal :=
        by
  classical
  have hbound : 2 * half + 1 < n := by have := ideal.card_lt hproper; omega
  have hconjugate := second_terminal_conjugate n hthree half hbound
  dsimp only at hconjugate
  split_ifs at hconjugate ⊢ with heven
  · exact dominant_iff_terminal ideal half hcard hproper _ _ _ (Or.inr ⟨rfl, rfl⟩)
      hconjugate.symm
  · exact dominant_iff_terminal ideal half hcard hproper _ _ _ (Or.inr ⟨rfl, rfl⟩)
      hconjugate.symm

/-- A proper odd-cardinality Hessenberg ideal has a unique dominant simple vector. -/
theorem dominant_odd_unique (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    ∃! alpha : PositiveRoot n,
      (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) ∧
        ideal.IsDominant alpha := by
  classical
  have hbound : 2 * half + 1 < n := by have := ideal.card_lt hproper; omega
  have hchoice := ideal.terminal_choice half hcard hbound
  have hexclusive : ideal.IsDominant (simpleRoot n hthree 0) ↔
      ¬ideal.IsDominant (simpleRoot n hthree 1) := by
    rw [ideal.dominant_first_iff half hcard hproper, ideal.dominant_second_iff half hcard hproper]
    split_ifs <;> tauto
  by_cases hfirst : ideal.IsDominant (simpleRoot n hthree 0)
  · refine ⟨simpleRoot n hthree 0, ⟨Or.inl rfl, hfirst⟩, ?_⟩
    intro alpha halpha
    rcases halpha.1 with hzero | hone
    · exact hzero
    · subst alpha
      exact False.elim ((hexclusive.mp hfirst) halpha.2)
  · have hsecond : ideal.IsDominant (simpleRoot n hthree 1) := by tauto
    refine ⟨simpleRoot n hthree 1, ⟨Or.inr rfl, hsecond⟩, ?_⟩
    intro alpha halpha
    rcases halpha.1 with hzero | hone
    · subst alpha
      exact False.elim (hfirst halpha.2)
    · exact hone

end Schubert.DihedralSplines.HessenbergIdeal
