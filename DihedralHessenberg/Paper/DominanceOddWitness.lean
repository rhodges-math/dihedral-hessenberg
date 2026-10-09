import DihedralHessenberg.Paper.DominanceEven
import DihedralHessenberg.Paper.RootConjugateEdge
import DihedralHessenberg.Paper.HessenbergSupport
import DihedralHessenberg.Dihedral.RootReflectionVectors
import DihedralHessenberg.Dihedral.RootReflectionLengthVectors

/-! # Canonical lengths of odd-cardinality dominance witnesses -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem witness_size (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (size : ℕ) (hpositive : 0 < size) (hsize : size ≤ n)
    (hconditions : let element := beta.alternatingProduct alpha size
      ideal.toRootSubset.length element = ideal.carrier.ncard / 2 ∧
        (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ∧
        (element, beta.reflection * element) ∉ ideal.toRootSubset.edges) :
    size = n - half - 1 := by
  let element := beta.alternatingProduct alpha size
  rcases hconditions with ⟨hdegree, hedge, hnot⟩
  have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
      (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
    rcases hpair with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  have halphaSimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1 :=
    hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hbetaSimple : beta = simpleRoot n hthree 0 ∨ beta = simpleRoot n hthree 1 :=
    hpair.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hlength : length n hthree element = size :=
    PositiveRoot.alternating_length beta alpha hreverse size hsize
  have hmaximum := ideal.card_lt hproper
  have hhalfCard : 2 * half ≤ ideal.indexed.roots.card := by
    rw [← ideal.ncard_indexed, hcard]
    omega
  have hshort : size < n := by
    by_contra hlong
    have heq : element = longestElement n hthree :=
      (length_eq_longest n hthree element).mp (by omega)
    change ideal.toRootSubset.length element = ideal.carrier.ncard / 2 at hdegree
    rw [heq, ideal.length_top, hcard] at hdegree
    omega
  have hascent : length n hthree (alpha.reflection * element) = size + 1 :=
    PositiveRoot.alternating_ascent alpha beta hpair size (by omega)
  have hdescent : length n hthree (beta.reflection * element) + 1 = size :=
    PositiveRoot.alternating_descent alpha beta hpair size hpositive hsize
  have hupper : size ≤ n - half - 1 := by
    by_contra hlarge
    have hupperDegree := HessenbergSpace.LengthRanges.card_sub_complementary ideal.indexed
      half hhalfCard element (by rw [hlength]; omega)
    rw [← ideal.length_indexed, ← ideal.ncard_indexed, hlength] at hupperDegree
    change ideal.toRootSubset.length element = ideal.carrier.ncard / 2 at hdegree
    rw [hcard] at hupperDegree hdegree hmaximum
    omega
  have hdegreeBound := ideal.indexed.length_le_coxeter_length element
  rw [← ideal.length_indexed, hlength] at hdegreeBound
  have hbelow : half ≤ size := by
    change ideal.toRootSubset.length element = ideal.carrier.ncard / 2 at hdegree
    rw [hcard] at hdegree
    omega
  obtain ⟨gamma, hselected, hneighbor⟩ := (ideal.toRootSubset.mem_edges _).mp hedge
  have hreflection := alpha.ascent_length hthree gamma halphaSimple element
    (bruhatLE_of_length_lt n hthree (by omega))
    (by intro heq; have := congrArg (length n hthree) heq; omega) hneighbor
  have hselectedLength := ideal.reflection_length_le gamma hselected
  rw [hreflection, hlength, hcard] at hselectedLength
  have houter : size ≤ half ∨ n - half - 1 ≤ size := by
    split_ifs at hselectedLength <;> omega
  rcases houter with hlow | hhigh
  · have hequal : size = half := by omega
    have hreflection := (beta.isReflection hthree).conj element⁻¹
    rw [inv_inv] at hreflection
    obtain ⟨delta, hdelta⟩ := (isReflection_iff_positiveRoot n hthree _).mp hreflection
    have hdeltaNeighbor : beta.reflection * element = element * delta.reflection := by
      rw [hdelta]
      group
    have hdeltaLength := beta.descent_length hthree delta hbetaSimple element
      (bruhatLE_of_length_lt n hthree (by omega))
      (by intro heq; have := congrArg (length n hthree) heq; omega) hdeltaNeighbor
    rw [hlength, hequal, ite_eq_left (by omega)] at hdeltaLength
    have hdeltaSelected := ideal.selected_of_short delta (by rw [hdeltaLength, hcard]; omega)
    exact False.elim (hnot ((ideal.toRootSubset.edge_iff_conjugate beta delta element hdelta).mpr
      hdeltaSelected))
  · omega

/-- Every dominant simple vector for a proper odd ideal has the same alternating witness size. -/
theorem dominant_odd_witness (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha : PositiveRoot n) (hdominant : ideal.IsDominant alpha) :
    ∃ beta : PositiveRoot n,
      ((alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
        (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) ∧
      let element := beta.alternatingProduct alpha (n - half - 1)
      ideal.toRootSubset.length element = ideal.carrier.ncard / 2 ∧
        (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ∧
        (element, beta.reflection * element) ∉ ideal.toRootSubset.edges := by
  obtain ⟨beta, hpair, size, hpositive, hsize, hconditions⟩ := hdominant
  have heq := witness_size ideal half hcard hproper alpha beta hpair
      size hpositive hsize hconditions
  subst size
  exact ⟨beta, hpair, hconditions⟩

end Schubert.DihedralSplines.HessenbergIdeal
