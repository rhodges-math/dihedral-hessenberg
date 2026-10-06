import Schubert.Dihedral.ConeInterior

/-! # The extremal positive roots of a compatible generic separator -/

namespace Schubert.Dihedral.Separator

/-- Every non-simple root lies farther into a compatible open half-plane than both simples. -/
theorem simple_extremal {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (hpositive : data.positive = positiveRoots n) (alpha : PositiveRoot n)
    (hfirst : alpha ≠ simpleRoot n hthree 0) (hsecond : alpha ≠ simpleRoot n hthree 1) :
    max (realBilinearForm (simpleRoot n hthree 0).val data.normal)
        (realBilinearForm (simpleRoot n hthree 1).val data.normal) <
      realBilinearForm alpha.val data.normal := by
  have first_mem : (simpleRoot n hthree 0).val ∈ data.positive := by
    rw [hpositive]
    exact (simpleRoot n hthree 0).property
  have second_mem : (simpleRoot n hthree 1).val ∈ data.positive := by
    rw [hpositive]
    exact (simpleRoot n hthree 1).property
  have hfirst_pos := first_mem.2
  have hsecond_pos := second_mem.2
  let a := rootConeCoordinates n alpha.index 0
  let b := rootConeCoordinates n alpha.index 1
  have ha : 1 ≤ a := coneCoordinates_interior n hthree alpha hfirst hsecond 0
  have hb : 1 ≤ b := coneCoordinates_interior n hthree alpha hfirst hsecond 1
  have hexpansion : alpha.val =
      a • (simpleRoot n hthree 0).val + b • (simpleRoot n hthree 1).val := by
    rw [simpleRoot_zero, simpleRoot_one, positiveRootEquiv_val, positiveRootEquiv_val,
      ← positiveRoot_eq_rootConeCoordinates n hthree alpha.index, PositiveRoot.index_val]
  have hpairing : realBilinearForm alpha.val data.normal =
      a * realBilinearForm (simpleRoot n hthree 0).val data.normal +
        b * realBilinearForm (simpleRoot n hthree 1).val data.normal := by
    rw [hexpansion]
    simp only [realBilinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : realBilinearForm (simpleRoot n hthree 0).val data.normal +
      realBilinearForm (simpleRoot n hthree 1).val data.normal ≤
        realBilinearForm alpha.val data.normal := by
    rw [hpairing]
    have hmul_first := mul_le_mul_of_nonneg_right ha hfirst_pos.le
    have hmul_second := mul_le_mul_of_nonneg_right hb hsecond_pos.le
    simp only [one_mul] at hmul_first hmul_second
    linarith
  exact max_lt (by linarith) (by linarith)

/-- The chosen simple vectors are the unique pair nearest a compatible generic hyperplane. -/
theorem closest_pair {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (hpositive : data.positive = positiveRoots n) :
    ∃! pair : Finset RealPlane, pair.card = 2 ∧ (↑pair : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ pair, ∀ second ∈ data.positive, second ∉ pair →
        realBilinearForm first data.normal < realBilinearForm second data.normal := by
  classical
  let first := (simpleRoot n hthree 0).val
  let second := (simpleRoot n hthree 1).val
  let pair : Finset RealPlane := {first, second}
  have hne : first ≠ second := by
    intro heq
    have hroot := Subtype.ext heq
    rw [simpleRoot_zero, simpleRoot_one] at hroot
    have hindex := (positiveRootEquiv n).injective hroot
    have hval := congrArg Fin.val hindex
    norm_num [firstSimpleRootIndex, secondSimpleRootIndex] at hval
  have hcard : pair.card = 2 := by simp [pair, hne]
  have hpairmem (vector : RealPlane) : vector ∈ pair ↔ vector = first ∨ vector = second := by
    simp [pair]
  have hsubset : (↑pair : Set RealPlane) ⊆ data.positive := by
    intro vector hmem
    rw [hpositive]
    rcases (hpairmem _).mp hmem with rfl | rfl
    · exact (simpleRoot n hthree 0).property
    · exact (simpleRoot n hthree 1).property
  have hextremal : ∀ root ∈ pair, ∀ vector ∈ data.positive, vector ∉ pair →
      realBilinearForm root data.normal < realBilinearForm vector data.normal := by
    intro root hroot vector hvector hout
    have hcanonical : vector ∈ positiveRoots n := hpositive ▸ hvector
    let alpha : PositiveRoot n := ⟨vector, hcanonical⟩
    have ha : alpha ≠ simpleRoot n hthree 0 := by
      intro heq
      exact hout ((hpairmem _).mpr (Or.inl (congrArg Subtype.val heq)))
    have hb : alpha ≠ simpleRoot n hthree 1 := by
      intro heq
      exact hout ((hpairmem _).mpr (Or.inr (congrArg Subtype.val heq)))
    have hlt := data.simple_extremal hthree hpositive alpha ha hb
    rcases (hpairmem _).mp hroot with rfl | rfl
    · exact lt_of_le_of_lt (le_max_left _ _) hlt
    · exact lt_of_le_of_lt (le_max_right _ _) hlt
  refine ⟨pair, ⟨hcard, hsubset, hextremal⟩, ?_⟩
  intro other hother
  apply Finset.eq_of_subset_of_card_le
  · intro vector hvector
    by_contra hout
    have hfirst : first ∈ other := by
      by_contra hnot
      have hforward := hextremal first (by simp [pair]) vector (hother.2.1 hvector) hout
      have hback := hother.2.2 vector hvector first (hsubset (by simp [pair])) hnot
      linarith
    have hsecond : second ∈ other := by
      by_contra hnot
      have hforward := hextremal second (by simp [pair]) vector (hother.2.1 hvector) hout
      have hback := hother.2.2 vector hvector second (hsubset (by simp [pair])) hnot
      linarith
    have hsub : pair ⊆ other := by
      intro root hroot
      rcases (hpairmem _).mp hroot with rfl | rfl
      · exact hfirst
      · exact hsecond
    have heq : pair = other := Finset.eq_of_subset_of_card_le hsub (by
      rw [hcard, hother.1])
    exact hout (heq.symm ▸ hvector)
  · rw [hcard, hother.1]

end Schubert.Dihedral.Separator
