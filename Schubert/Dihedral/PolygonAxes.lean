import Schubert.Dihedral.PolygonVertices

/-! # The displayed polygon rays and reflection axes -/

noncomputable section

namespace Schubert.Dihedral

private def axisShift (n : ℕ) : ℕ :=
  if Even n then n / 2 + 1 else (n + 1) / 2

private theorem axisShift_lt (n : ℕ) (hthree : 3 ≤ n) : axisShift n < n := by
  unfold axisShift
  split_ifs with heven
  · obtain ⟨half, hhalf⟩ := heven
    omega
  · omega

private theorem offset_shift (n : ℕ) (hthree : 3 ≤ n) :
    polygonOffset n + axisShift n * Real.pi / n = Real.pi / 2 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold polygonOffset axisShift
  split_ifs with heven
  · have hsize : (2 : ℝ) * (n / 2 : ℕ) = n := by
      obtain ⟨half, hhalf⟩ := heven
      exact_mod_cast (show 2 * (n / 2) = n by omega)
    push_cast
    field_simp [hn]
    nlinarith
  · have hsize : (2 : ℝ) * ((n + 1) / 2 : ℕ) = n + 1 := by
      obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
      exact_mod_cast (show 2 * ((n + 1) / 2) = n + 1 by omega)
    field_simp [hn]
    nlinarith

/-- Every root's orthogonal unit direction occurs among the displayed polygon rays. -/
theorem PositiveRoot.axis_drawn {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    ∃ ray : Fin (2 * n), ![-alpha.val 1, alpha.val 0] =
      unitRootAt (polygonOffset n + ray.val * Real.pi / n) := by
  refine ⟨⟨angularIndex alpha.index + axisShift n, by
    have := angularIndex_lt alpha.index
    have := axisShift_lt n hthree
    omega⟩, ?_⟩
  have hangle : polygonOffset n + (angularIndex alpha.index + axisShift n : ℕ) *
      Real.pi / n = rootAngle n alpha.index + Real.pi / 2 := by
    rw [rootAngle_eq_angularIndex, ← offset_shift n hthree]
    push_cast
    ring
  change ![-alpha.val 1, alpha.val 0] =
    unitRootAt (polygonOffset n + (angularIndex alpha.index + axisShift n : ℕ) * Real.pi / n)
  rw [hangle, ← alpha.index_val]
  apply realPlane_ext <;> simp [positiveRoot, unitRootAt, Real.cos_add, Real.sin_add]

/-- Each displayed real ray lies on a root-reflection fixed axis. -/
theorem drawn_axis_fixed (n : ℕ) (hthree : 3 ≤ n) (ray : Fin (2 * n)) (scalar : ℝ) :
    ∃ alpha : PositiveRoot n,
      realAction n alpha.reflection
          (scalar • unitRootAt (polygonOffset n + ray.val * Real.pi / n)) =
        scalar • unitRootAt (polygonOffset n + ray.val * Real.pi / n) := by
  let position := (ray.val + n - axisShift n) % n
  have hn : 0 < n := by omega
  have hposition : position < n := Nat.mod_lt _ hn
  obtain ⟨index, hindex⟩ := angularIndex_surjective n ⟨position, hposition⟩
  refine ⟨positiveRootEquiv n index, ?_⟩
  apply (PositiveRoot.reflection_fixed _ _).mpr
  have hbound : axisShift n ≤ ray.val + n := by have := axisShift_lt n hthree; omega
  have hdivision : (position : ℝ) + n * ((ray.val + n - axisShift n) / n : ℕ) =
      ray.val + n - axisShift n := by
    have hdivision := Nat.mod_add_div (ray.val + n - axisShift n) n
    have hcast := congrArg (fun value : ℕ => (value : ℝ)) hdivision
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbound] using hcast
  have hangle : polygonOffset n + ray.val * Real.pi / n - rootAngle n index =
      Real.pi / 2 + (((ray.val + n - axisShift n) / n : ℕ) - (1 : ℝ)) * Real.pi := by
    rw [rootAngle_eq_angularIndex, hindex]
    have hoffset := offset_shift n hthree
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hnreal] at hoffset ⊢
    have hscaled := congrArg (fun value : ℝ => value * Real.pi) hdivision
    nlinarith
  have horthogonal : realBilinearForm
      (unitRootAt (polygonOffset n + ray.val * Real.pi / n)) (positiveRootEquiv n index).val =
        0 := by
    rw [positiveRootEquiv_val]
    simp only [positiveRoot, unitRootAt, realBilinearForm, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← Real.cos_sub]
    rw [hangle, sub_mul, one_mul, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.sin_sub, Real.sin_nat_mul_pi, Real.sin_pi]
    ring
  have hscalar : realBilinearForm
      (scalar • unitRootAt (polygonOffset n + ray.val * Real.pi / n))
        (positiveRootEquiv n index).val = scalar * realBilinearForm
          (unitRootAt (polygonOffset n + ray.val * Real.pi / n))
            (positiveRootEquiv n index).val := by
    simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hscalar, horthogonal, mul_zero]

end Schubert.Dihedral
