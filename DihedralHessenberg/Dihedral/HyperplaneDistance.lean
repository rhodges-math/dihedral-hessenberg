import DihedralHessenberg.Dihedral.ClosestRoots

/-! # Euclidean distances of unit roots from generic hyperplanes -/

noncomputable section

namespace Schubert.Dihedral.Separator

/-- The Euclidean distance of a real vector from the hyperplane with the given normal. -/
def distance {n : ℕ} (data : Separator n) (vector : RealPlane) : ℝ :=
  |realBilinearForm vector data.normal| /
    Real.sqrt (realBilinearForm data.normal data.normal)

private theorem normal_norm_pos {n : ℕ} (data : Separator n) (hthree : 3 ≤ n) :
    0 < realBilinearForm data.normal data.normal := by
  have hnonzero : data.normal ≠ 0 := by
    intro heq
    have h := data.generic (simpleRoot n hthree 0).val
      (Or.inl (simpleRoot n hthree 0).property)
    simp only [heq, realBilinearForm, Pi.zero_apply, mul_zero, add_zero, ne_eq,
      not_true_eq_false] at h
  by_contra hnot
  have hfirst : data.normal 0 = 0 := by
    simp only [realBilinearForm] at hnot
    nlinarith [sq_nonneg (data.normal 1)]
  have hsecond : data.normal 1 = 0 := by
    simp only [realBilinearForm] at hnot
    nlinarith [sq_nonneg (data.normal 0)]
  apply hnonzero
  funext coordinate
  fin_cases coordinate
  · exact hfirst
  · exact hsecond

/-- The orthogonal projection onto the hyperplane through the origin. -/
def foot {n : ℕ} (data : Separator n) (vector : RealPlane) : RealPlane :=
  vector - (realBilinearForm vector data.normal /
    realBilinearForm data.normal data.normal) • data.normal

/-- The orthogonal projection lies on the separating hyperplane. -/
theorem foot_pairing {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (vector : RealPlane) : realBilinearForm (data.foot vector) data.normal = 0 := by
  let coefficient := realBilinearForm vector data.normal /
    realBilinearForm data.normal data.normal
  have hmul : coefficient * realBilinearForm data.normal data.normal =
      realBilinearForm vector data.normal := div_mul_cancel₀ _
        (ne_of_gt (data.normal_norm_pos hthree))
  change realBilinearForm (vector - coefficient • data.normal) data.normal = 0
  simp only [realBilinearForm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  nlinarith only [hmul]

/-- The squared Euclidean distance equals the squared length of the projection displacement. -/
theorem distance_sq {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (vector : RealPlane) :
    data.distance vector ^ 2 =
      realBilinearForm (vector - data.foot vector) (vector - data.foot vector) := by
  have hpos := data.normal_norm_pos hthree
  let coefficient := realBilinearForm vector data.normal /
    realBilinearForm data.normal data.normal
  have hmul : coefficient * realBilinearForm data.normal data.normal =
      realBilinearForm vector data.normal := div_mul_cancel₀ _ (ne_of_gt hpos)
  rw [distance, div_pow, sq_abs, Real.sq_sqrt (le_of_lt hpos), foot, sub_sub_cancel]
  apply (div_eq_iff (ne_of_gt hpos)).mpr
  change realBilinearForm vector data.normal ^ 2 =
    realBilinearForm (coefficient • data.normal) (coefficient • data.normal) *
      realBilinearForm data.normal data.normal
  rw [← hmul]
  simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every point on the hyperplane is at least the projection distance from the vector. -/
theorem distance_min {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (vector point : RealPlane) (hpoint : realBilinearForm point data.normal = 0) :
    data.distance vector ^ 2 ≤ realBilinearForm (vector - point) (vector - point) := by
  have hpos := data.normal_norm_pos hthree
  rw [distance, div_pow, sq_abs, Real.sq_sqrt (le_of_lt hpos)]
  apply (div_le_iff₀ hpos).mpr
  have hcross := sq_nonneg
    ((vector 0 - point 0) * data.normal 1 - (vector 1 - point 1) * data.normal 0)
  simp only [realBilinearForm, Pi.sub_apply] at *
  have hpair : vector 0 * data.normal 0 + vector 1 * data.normal 1 =
      (vector 0 - point 0) * data.normal 0 +
        (vector 1 - point 1) * data.normal 1 := by
    linarith only [hpoint]
  rw [hpair]
  nlinarith only [hcross]

/-- Distance comparisons on the positive side are exactly comparisons of normal pairings. -/
theorem distance_lt {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (first second : RealPlane) (hfirst : first ∈ data.positive)
    (hsecond : second ∈ data.positive) :
    data.distance first < data.distance second ↔
      realBilinearForm first data.normal < realBilinearForm second data.normal := by
  rw [distance, distance, abs_of_pos hfirst.2, abs_of_pos hsecond.2,
    div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr (data.normal_norm_pos hthree))]

/-- Every generic hyperplane has a unique two-root subset strictly closest in Euclidean distance. -/
theorem unique_nearest_pair {n : ℕ} (data : Separator n) (hthree : 3 ≤ n) :
    ∃! pair : Finset RealPlane, pair.card = 2 ∧ (↑pair : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ pair, ∀ second ∈ data.positive, second ∉ pair →
        data.distance first < data.distance second := by
  let P := fun pair : Finset RealPlane => pair.card = 2 ∧
    (↑pair : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ pair, ∀ second ∈ data.positive, second ∉ pair →
        realBilinearForm first data.normal < realBilinearForm second data.normal
  let Q := fun pair : Finset RealPlane => pair.card = 2 ∧
    (↑pair : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ pair, ∀ second ∈ data.positive, second ∉ pair →
        data.distance first < data.distance second
  have hiff (pair : Finset RealPlane) : P pair ↔ Q pair := by
    constructor
    · rintro ⟨hcard, hsubset, hclosest⟩
      refine ⟨hcard, hsubset, ?_⟩
      intro first hfirst second hsecond hout
      exact (data.distance_lt hthree first second (hsubset hfirst) hsecond).mpr
        (hclosest first hfirst second hsecond hout)
    · rintro ⟨hcard, hsubset, hclosest⟩
      refine ⟨hcard, hsubset, ?_⟩
      intro first hfirst second hsecond hout
      exact (data.distance_lt hthree first second (hsubset hfirst) hsecond).mp
        (hclosest first hfirst second hsecond hout)
  exact ((Equiv.refl (Finset RealPlane)).existsUnique_congr hiff).mp
    (data.unique_closest_pair hthree)

end Schubert.Dihedral.Separator
