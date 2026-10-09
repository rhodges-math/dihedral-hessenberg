import DihedralHessenberg.Dihedral.LengthParity
import DihedralHessenberg.Paper.PaperFull

/-! # Boundary degrees of full-root upper ideals -/

namespace Schubert.Dihedral.RootSubset

/-- Full-root endpoints are adjacent precisely at opposite canonical length parity. -/
theorem full_edge_parity (n : ℕ) (hthree : 3 ≤ n)
    (source target : DihedralGroup n) :
    (source, target) ∈ (full n).edges ↔
      Schubert.Dihedral.length n hthree source % 2 ≠
        Schubert.Dihedral.length n hthree target % 2 := by
  let : NeZero n := ⟨by omega⟩
  have heq : (source, target) ∈ (full n).edges ↔
      ∃ alpha : PositiveRoot n, alpha.reflection = source⁻¹ * target := by
    rw [mem_edges]
    constructor
    · rintro ⟨alpha, _, htarget⟩
      refine ⟨alpha, ?_⟩
      change target = source * alpha.reflection at htarget
      rw [htarget]
      group
    · rintro ⟨alpha, halpha⟩
      refine ⟨alpha, alpha.property, ?_⟩
      rw [halpha]
      group
  rw [heq, positiveReflection_iff_odd n hthree, Nat.odd_iff]
  have hparity := (coxeterSystem n hthree).length_mul_mod_two source⁻¹ target
  change Schubert.Dihedral.length n hthree (source⁻¹ * target) % 2 =
    (Schubert.Dihedral.length n hthree source⁻¹ +
      Schubert.Dihedral.length n hthree target) % 2 at hparity
  rw [length_inv] at hparity
  omega

/-- Every vertex in a full-root upper ideal has boundary degree equal to its minimum length. -/
theorem ncard_upper_boundary (n : ℕ) (hthree : 3 ≤ n)
    (element source : DihedralGroup n) (hsource : BruhatLE n hthree element source) :
    {target : DihedralGroup n | (source, target) ∈ (full n).edges ∧
      ¬BruhatLE n hthree element target}.ncard = Schubert.Dihedral.length n hthree element := by
  classical
  let : NeZero n := ⟨by omega⟩
  let ball := Finset.univ.filter fun target : DihedralGroup n =>
    Schubert.Dihedral.length n hthree target ≤ Schubert.Dihedral.length n hthree element ∧
      Schubert.Dihedral.length n hthree target % 2 ≠ Schubert.Dihedral.length n hthree source % 2
  have hset : {target : DihedralGroup n | (source, target) ∈ (full n).edges ∧
      ¬BruhatLE n hthree element target} = (ball.erase element : Set (DihedralGroup n)) := by
    ext target
    by_cases hsame : target = element
    · subst target
      simp only [Set.mem_ofPred_eq, bruhatLE_refl, not_true_eq_false, and_false,
        Finset.mem_coe, Finset.mem_erase, ne_eq, not_true_eq_false, false_and]
    · simp only [Set.mem_ofPred_eq, full_edge_parity n hthree source target,
        bruhatLE_iff_eq_or_length_lt,
        Finset.mem_coe, Finset.mem_erase, ball, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Ne.symm hsame, false_or, not_lt]
      constructor
      · rintro ⟨hparity, hlength⟩
        exact ⟨hsame, hlength, hparity.symm⟩
      · rintro ⟨_, hlength, hparity⟩
        exact ⟨hparity.symm, hlength⟩
  rw [hset, Set.ncard_coe_finset]
  have helementBound := length_le_polygon_parameter n hthree element
  have hsourceBound := length_le_polygon_parameter n hthree source
  have hsourceLength := bruhatLE_length_le n hthree hsource
  by_cases htop : Schubert.Dihedral.length n hthree element = n
  · have htopSource : Schubert.Dihedral.length n hthree source = n := by omega
    have hnot : element ∉ ball := by
      simp only [ball, Finset.mem_filter, Finset.mem_univ, htop, htopSource,
        ne_eq, not_true_eq_false, and_false, not_false_eq_true]
    have hball : ball = Finset.univ.filter (fun target : DihedralGroup n =>
        Schubert.Dihedral.length n hthree target % 2 ≠
          Schubert.Dihedral.length n hthree source % 2) := by
      ext target
      have hbound := length_le_polygon_parameter n hthree target
      simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, htop]
      omega
    rw [Finset.erase_eq_of_notMem hnot, hball,
      card_parity_all n hthree _ (Nat.mod_lt _ (by decide))]
    exact htop.symm
  · have hshort : Schubert.Dihedral.length n hthree element < n := by omega
    have hball := card_parity_ball n hthree (Schubert.Dihedral.length n hthree element)
      (Schubert.Dihedral.length n hthree source % 2) hshort (Nat.mod_lt _ (by decide))
    change ball.card = Schubert.Dihedral.length n hthree element +
      if Schubert.Dihedral.length n hthree element % 2 ≠
        Schubert.Dihedral.length n hthree source % 2 then 1 else 0 at hball
    by_cases hparity : Schubert.Dihedral.length n hthree element % 2 ≠
      Schubert.Dihedral.length n hthree source % 2
    · have hmem : element ∈ ball := by simp [ball, hparity]
      rw [Finset.card_erase_of_mem hmem, hball, ite_eq_left hparity]
      omega
    · have hnot : element ∉ ball := by simp [ball, hparity]
      rw [Finset.erase_eq_of_notMem hnot, hball, ite_eq_right hparity, Nat.add_zero]

end Schubert.Dihedral.RootSubset
