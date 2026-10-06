import Schubert.DihedralSplines.FullUpperBoundary
import Schubert.DihedralSplines.UpperConnectivity

/-! # Left-root coordinates of full upper-ideal boundaries -/

namespace Schubert.Dihedral.RootSubset

/-- A left-reflection target outside an upper ideal descends from every vertex in that ideal. -/
theorem left_boundary_descends (n : ℕ) (hthree : 3 ≤ n)
    (minimum current : DihedralGroup n) (hcurrent : BruhatLE n hthree minimum current)
    (alpha : PositiveRoot n) (hout : ¬BruhatLE n hthree minimum (alpha.reflection * current)) :
    Schubert.Dihedral.length n hthree (alpha.reflection * current) <
      Schubert.Dihedral.length n hthree current := by
  have hminimum := bruhatLE_length_le n hthree hcurrent
  have hne := (alpha.isReflection hthree).length_mul_right_ne current
  change Schubert.Dihedral.length n hthree (alpha.reflection * current) ≠
    Schubert.Dihedral.length n hthree current at hne
  by_contra hnot
  apply hout
  apply (bruhatLE_iff_eq_or_length_lt n hthree _ _).mpr
  right
  omega

/-- Left positive reflections biject onto the outgoing upper-boundary endpoints. -/
theorem left_boundary_bijOn (n : ℕ) (hthree : 3 ≤ n)
    (minimum current : DihedralGroup n) (hcurrent : BruhatLE n hthree minimum current) :
    Set.BijOn (fun alpha : PositiveRoot n => alpha.reflection * current)
      {alpha | Schubert.Dihedral.length n hthree (alpha.reflection * current) <
        Schubert.Dihedral.length n hthree current ∧
        ¬BruhatLE n hthree minimum (alpha.reflection * current)}
      {target | (current, target) ∈ (full n).edges ∧ ¬BruhatLE n hthree minimum target} := by
  constructor
  · intro alpha halpha
    exact ⟨full_left_edge n hthree alpha current, halpha.2⟩
  constructor
  · intro alpha _ beta _ heq
    exact PositiveRoot.reflection_injective n (mul_right_cancel heq)
  · intro target htarget
    obtain ⟨beta, _, hbeta⟩ := ((full n).mem_edges _).mp htarget.1
    change target = current * beta.reflection at hbeta
    have hreflection := (beta.isReflection hthree).conj current
    obtain ⟨alpha, halpha⟩ := (isReflection_iff_positiveRoot n hthree _).mp hreflection
    have heq : alpha.reflection * current = target := by rw [halpha, hbeta]; group
    have hout : ¬BruhatLE n hthree minimum (alpha.reflection * current) := heq ▸ htarget.2
    exact ⟨alpha, ⟨left_boundary_descends n hthree minimum current hcurrent alpha hout, hout⟩,
      heq⟩

open scoped Classical in
/-- The finite left-root boundary filter has cardinality equal to the upper minimum length. -/
theorem card_left_upper_boundary (n : ℕ) (hthree : 3 ≤ n)
    (minimum current : DihedralGroup n) (hcurrent : BruhatLE n hthree minimum current) :
    (Finset.univ.filter fun alpha : PositiveRoot n =>
      Schubert.Dihedral.length n hthree (alpha.reflection * current) <
        Schubert.Dihedral.length n hthree current ∧
        ¬BruhatLE n hthree minimum (alpha.reflection * current)).card =
      Schubert.Dihedral.length n hthree minimum := by
  classical
  have hcard := (left_boundary_bijOn n hthree minimum current hcurrent).ncard_eq
  rw [ncard_upper_boundary n hthree minimum current hcurrent] at hcard
  have hset : {alpha : PositiveRoot n |
      Schubert.Dihedral.length n hthree (alpha.reflection * current) <
        Schubert.Dihedral.length n hthree current ∧
        ¬BruhatLE n hthree minimum (alpha.reflection * current)} =
      (Finset.univ.filter (fun alpha : PositiveRoot n =>
        Schubert.Dihedral.length n hthree (alpha.reflection * current) <
          Schubert.Dihedral.length n hthree current ∧
          ¬BruhatLE n hthree minimum (alpha.reflection * current)) : Set (PositiveRoot n)) := by
    ext alpha
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset, Set.ncard_coe_finset] at hcard
  exact hcard

end Schubert.Dihedral.RootSubset
