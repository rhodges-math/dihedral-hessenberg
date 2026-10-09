import DihedralHessenberg.Dihedral.RootLatticeRescaling

/-! # Root-system axioms for positive conjugacy-invariant radial configurations -/

namespace Schubert.Dihedral.RootLattice

private theorem norm_scale (scalar : ℝ) (vector : RealPlane) :
    realBilinearForm (scalar • vector) (scalar • vector) =
      scalar ^ 2 * realBilinearForm vector vector := by
  simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul]
  ring

private theorem normal_neg (normal vector : RealPlane) :
    vector - (2 * realBilinearForm vector (-normal) /
      realBilinearForm (-normal) (-normal)) • (-normal) =
    vector - (2 * realBilinearForm vector normal /
      realBilinearForm normal normal) • normal := by
  funext coordinate
  simp only [realBilinearForm, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

private theorem vector_neg (normal vector : RealPlane) :
    -vector - (2 * realBilinearForm (-vector) normal /
      realBilinearForm normal normal) • normal =
    -(vector - (2 * realBilinearForm vector normal /
      realBilinearForm normal normal) • normal) := by
  funext coordinate
  simp only [realBilinearForm, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Negation preserves each signed root configuration. -/
theorem neg_mem (lattice : RootLattice) (vector : RealPlane) :
    -vector ∈ lattice.roots ↔ vector ∈ lattice.roots := by
  simp only [roots, Set.mem_union, Set.mem_ofPred_eq, neg_neg]
  exact or_comm

namespace Rescaling

variable {lattice : RootLattice} {n : ℕ}

/-- The complete signed radial carrier is finite. -/
theorem roots_finite (data : Rescaling lattice n) : lattice.roots.Finite := by
  have hnegative : {vector : RealPlane | -vector ∈ lattice.positive} =
      Neg.neg '' lattice.positive := by
    ext vector
    constructor
    · intro hvector
      exact ⟨-vector, hvector, neg_neg vector⟩
    · rintro ⟨other, hother, rfl⟩
      change - -other ∈ lattice.positive
      simpa only [neg_neg] using hother
  rw [roots, hnegative]
  exact data.finite.union (data.finite.image Neg.neg)

/-- All signed radial roots have positive Euclidean square norm. -/
theorem norm_pos (data : Rescaling lattice n) (vector : RealPlane)
    (hvector : vector ∈ lattice.roots) : 0 < realBilinearForm vector vector := by
  have hpositive (vector : RealPlane) (hvector : vector ∈ lattice.positive) :
      0 < realBilinearForm vector vector := by
    rw [data.carrier] at hvector
    obtain ⟨alpha, rfl⟩ := hvector
    rw [norm_scale, roots_unit alpha.val (Or.inl alpha.property), mul_one]
    exact sq_pos_of_pos (data.positive alpha)
  rcases hvector with hvector | hvector
  · exact hpositive vector hvector
  · have hnorm := hpositive (-vector) hvector
    simpa only [realBilinearForm, Pi.neg_apply, neg_mul_neg] using hnorm

/-- The signed radial configuration is closed under every one of its normal reflections. -/
theorem reflection_mem [NeZero n] (data : Rescaling lattice n)
    (normal vector : RealPlane) (hnormal : normal ∈ lattice.roots)
    (hvector : vector ∈ lattice.roots) :
    vector - (2 * realBilinearForm vector normal /
      realBilinearForm normal normal) • normal ∈ lattice.roots := by
  have hpositive (normal vector : RealPlane) (hnormal : normal ∈ lattice.positive)
      (hvector : vector ∈ lattice.positive) :
      vector - (2 * realBilinearForm vector normal /
        realBilinearForm normal normal) • normal ∈ lattice.roots := by
    rw [data.carrier] at hnormal hvector
    obtain ⟨alpha, rfl⟩ := hnormal
    obtain ⟨beta, rfl⟩ := hvector
    have hclosed := PositiveRoot.scaled_reflection_closed data.radius
      data.positive data.conjugate alpha beta
    rcases hclosed with hclosed | hclosed
    · exact Or.inl (data.carrier.symm ▸ hclosed)
    · exact Or.inr (data.carrier.symm ▸ hclosed)
  rcases hnormal with hnormal | hnormal
  · rcases hvector with hvector | hvector
    · exact hpositive normal vector hnormal hvector
    · have hclosed := hpositive normal (-vector) hnormal hvector
      rw [vector_neg, neg_mem] at hclosed
      exact hclosed
  · rcases hvector with hvector | hvector
    · have hclosed := hpositive (-normal) vector hnormal hvector
      rw [normal_neg] at hclosed
      exact hclosed
    · have hclosed := hpositive (-normal) (-vector) hnormal hvector
      rw [normal_neg, vector_neg, neg_mem] at hclosed
      exact hclosed

/-- Proportional positive radial roots are equal and have proportionality scalar one. -/
theorem positive_proportional (data : Rescaling lattice n) (alpha beta : PositiveRoot n)
    (scalar : ℝ) (heq : data.radius alpha • alpha.val =
      scalar • (data.radius beta • beta.val)) : alpha = beta ∧ scalar = 1 := by
  have hradius : data.radius alpha ≠ 0 := ne_of_gt (data.positive alpha)
  have hunit := congrArg (fun vector : RealPlane => (data.radius alpha)⁻¹ • vector) heq
  simp only [smul_smul, inv_mul_cancel₀ hradius, one_smul] at hunit
  have hcoefficient := roots_proportional alpha.val beta.val
    (Or.inl alpha.property) (Or.inl beta.property) _ hunit
  rcases hcoefficient with hcoefficient | hcoefficient
  · rw [hcoefficient, one_smul] at hunit
    have hequal : alpha = beta := Subtype.ext hunit
    subst beta
    refine ⟨rfl, ?_⟩
    field_simp at hcoefficient
    nlinarith [data.positive alpha]
  · rw [hcoefficient, neg_one_smul] at hunit
    have hbad := positiveRoot_ne_neg n alpha.index beta.index
    rw [alpha.index_val, beta.index_val] at hbad
    exact False.elim (hbad hunit)

/-- The signed radial configuration is reduced: proportional roots differ only by sign. -/
theorem reduced (data : Rescaling lattice n) (first second : RealPlane)
    (hfirst : first ∈ lattice.roots) (hsecond : second ∈ lattice.roots)
    (scalar : ℝ) (heq : first = scalar • second) : scalar = 1 ∨ scalar = -1 := by
  rcases hfirst with hfirst | hfirst
  · rw [data.carrier] at hfirst
    obtain ⟨alpha, rfl⟩ := hfirst
    rcases hsecond with hsecond | hsecond
    · rw [data.carrier] at hsecond
      obtain ⟨beta, rfl⟩ := hsecond
      exact Or.inl (data.positive_proportional alpha beta scalar heq).2
    · rw [data.carrier] at hsecond
      obtain ⟨beta, hbeta⟩ := hsecond
      have hsecond : second = -(data.radius beta • beta.val) := by
        simpa only [neg_neg] using congrArg Neg.neg hbeta.symm
      rw [hsecond, smul_neg, ← neg_smul] at heq
      have := (data.positive_proportional alpha beta (-scalar) heq).2
      right
      linarith
  · rw [data.carrier] at hfirst
    obtain ⟨alpha, halpha⟩ := hfirst
    have hfirst : first = -(data.radius alpha • alpha.val) := by
      simpa only [neg_neg] using congrArg Neg.neg halpha.symm
    have hneg := congrArg Neg.neg heq
    rw [hfirst, neg_neg] at hneg
    rcases hsecond with hsecond | hsecond
    · rw [data.carrier] at hsecond
      obtain ⟨beta, rfl⟩ := hsecond
      rw [← neg_smul] at hneg
      have := (data.positive_proportional alpha beta (-scalar) hneg).2
      right
      linarith
    · rw [data.carrier] at hsecond
      obtain ⟨beta, hbeta⟩ := hsecond
      have hsecond : second = -(data.radius beta • beta.val) := by
        simpa only [neg_neg] using congrArg Neg.neg hbeta.symm
      rw [hsecond, smul_neg, neg_neg] at hneg
      exact Or.inl (data.positive_proportional alpha beta scalar hneg).2

end Rescaling
end Schubert.Dihedral.RootLattice
