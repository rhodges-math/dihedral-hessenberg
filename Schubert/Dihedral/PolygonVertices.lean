import Schubert.Dihedral.UnitDirections

/-! # Regularly spaced polygon vertices and their reflection symmetry -/

noncomputable section

namespace Schubert.Dihedral

/-- The initial direction of the polygon, with a vertical reflection axis. -/
def polygonOffset (n : ℕ) : ℝ :=
  if Even n then -Real.pi / n else -Real.pi / (2 * n)

/-- The real vertices obtained by rotating the initial unit direction. -/
def polygonVertices (n : ℕ) : Set RealPlane :=
  Set.range fun coordinate : ZMod n =>
    realAction n (.r coordinate) (unitRootAt (polygonOffset n))

private theorem first_vertex_reflection (n : ℕ) (hthree : 3 ≤ n) :
    ∃ coordinate : ZMod n,
      realAction n (.sr 0) (unitRootAt (polygonOffset n)) =
        realAction n (.r coordinate) (unitRootAt (polygonOffset n)) := by
  let : NeZero n := ⟨by omega⟩
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  by_cases heven : Even n
  · refine ⟨((n / 2 + 1 : ℕ) : ZMod n), ?_⟩
    have hbound : n / 2 + 1 < n := by
      obtain ⟨half, hhalf⟩ := heven
      omega
    have hsize : (2 : ℝ) * (n / 2 : ℕ) = n := by
      obtain ⟨half, hhalf⟩ := heven
      exact_mod_cast (show 2 * (n / 2) = n by omega)
    rw [realAction_sr_unit, realAction_r_unit, polygonOffset, ite_eq_left heven,
      ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hbound]
    congr 1
    push_cast
    field_simp [hn]
    nlinarith
  · refine ⟨(((n + 1) / 2 : ℕ) : ZMod n), ?_⟩
    have hbound : (n + 1) / 2 < n := by omega
    have hsize : (2 : ℝ) * ((n + 1) / 2 : ℕ) = n + 1 := by
      obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
      exact_mod_cast (show 2 * ((n + 1) / 2) = n + 1 by omega)
    rw [realAction_sr_unit, realAction_r_unit, polygonOffset, ite_eq_right heven,
      ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hbound]
    congr 1
    push_cast
    field_simp [hn]
    nlinarith

/-- Every element of the concrete dihedral group preserves the polygon vertex set. -/
theorem polygon_action_mem (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (vector : RealPlane) (hvector : vector ∈ polygonVertices n) :
    realAction n element vector ∈ polygonVertices n := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨coordinate, rfl⟩ := hvector
  obtain ⟨shift, hshift⟩ := first_vertex_reflection n hthree
  cases element with
  | r exponent =>
    refine ⟨exponent + coordinate, ?_⟩
    rw [← realAction_mul_plane, DihedralGroup.r_mul_r]
  | sr exponent =>
    refine ⟨-(exponent + coordinate) + shift, ?_⟩
    rw [← realAction_mul_plane, DihedralGroup.sr_mul_r]
    have hnormal : DihedralGroup.sr (exponent + coordinate) =
        DihedralGroup.r (-(exponent + coordinate)) * DihedralGroup.sr 0 := by
      simp only [DihedralGroup.r_mul_sr, sub_neg_eq_add, zero_add]
    rw [hnormal, realAction_mul_plane, hshift, ← realAction_mul_plane,
      DihedralGroup.r_mul_r]

/-- Distinct modular rotations give distinct polygon vertices. -/
theorem polygon_vertex_injective (n : ℕ) (hthree : 3 ≤ n) :
    Function.Injective (fun coordinate : ZMod n =>
      realAction n (.r coordinate) (unitRootAt (polygonOffset n))) := by
  let : NeZero n := ⟨by omega⟩
  intro first second heq
  have hfixed := congrArg (realAction n (.r (-second))) heq
  rw [← realAction_mul_plane, ← realAction_mul_plane, DihedralGroup.r_mul_r,
    DihedralGroup.r_mul_r, neg_add_cancel, DihedralGroup.r_zero] at hfixed
  simp only [realAction_one, id_eq] at hfixed
  have hzero := rotation_fixed_unit n (-second + first) (unitRootAt (polygonOffset n))
    (realBilinearForm_unitRootAt _) hfixed
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg, add_comm] using hzero)

/-- The polygon has exactly n vertices. -/
theorem polygon_vertices_card (n : ℕ) (hthree : 3 ≤ n) : (polygonVertices n).ncard = n := by
  let : NeZero n := ⟨by omega⟩
  rw [polygonVertices, Set.ncard_range_of_injective (polygon_vertex_injective n hthree),
    Nat.card_eq_fintype_card, ZMod.card]


/-- The polygon vertices are exactly the n equally spaced unit directions. -/
theorem polygon_vertices_angles (n : ℕ) (hthree : 3 ≤ n) :
    polygonVertices n = Set.range (fun index : Fin n =>
      unitRootAt (2 * Real.pi * index.val / n + polygonOffset n)) := by
  let : NeZero n := ⟨by omega⟩
  ext vector
  constructor
  · rintro ⟨coordinate, hcoordinate⟩
    refine ⟨⟨coordinate.val, ZMod.val_lt coordinate⟩, ?_⟩
    change realAction n (.r coordinate) (unitRootAt (polygonOffset n)) = vector at hcoordinate
    rw [realAction_r_unit] at hcoordinate
    exact hcoordinate
  · rintro ⟨index, hindex⟩
    refine ⟨(index.val : ZMod n), ?_⟩
    change realAction n (.r (index.val : ZMod n)) (unitRootAt (polygonOffset n)) = vector
    rw [realAction_r_unit, ZMod.val_natCast, Nat.mod_eq_of_lt index.isLt]
    exact hindex

/-- The three small polygons use the displayed initial directions. -/
theorem polygon_small_offsets :
    polygonOffset 3 = -Real.pi / 6 ∧ polygonOffset 4 = -Real.pi / 4 ∧
      polygonOffset 5 = -Real.pi / 10 := by
  norm_num [polygonOffset, Nat.even_iff]


/-- All real dilates of the polygon vertex set are invariant under the group. -/
theorem polygon_scaled_action_mem (n : ℕ) (hthree : 3 ≤ n) (radius : ℝ)
    (element : DihedralGroup n) (vector : RealPlane)
    (hvector : vector ∈ (fun vertex => radius • vertex) '' polygonVertices n) :
    realAction n element vector ∈ (fun vertex => radius • vertex) '' polygonVertices n := by
  obtain ⟨vertex, hvertex, rfl⟩ := hvector
  refine ⟨realAction n element vertex, polygon_action_mem n hthree element vertex hvertex, ?_⟩
  exact (realAction_smul_plane n element radius vertex).symm

/-- Scaling the polygon gives exactly the equally spaced vertices at that radius. -/
theorem polygon_scaled_angles (n : ℕ) (hthree : 3 ≤ n) (radius : ℝ) :
    (fun vertex => radius • vertex) '' polygonVertices n =
      Set.range (fun index : Fin n =>
        radius • unitRootAt (2 * Real.pi * index.val / n + polygonOffset n)) := by
  rw [polygon_vertices_angles n hthree]
  ext vector
  constructor
  · rintro ⟨vertex, ⟨index, rfl⟩, hvertex⟩
    exact ⟨index, hvertex⟩
  · rintro ⟨index, hindex⟩
    exact ⟨unitRootAt (2 * Real.pi * index.val / n + polygonOffset n), ⟨index, rfl⟩, hindex⟩

end Schubert.Dihedral
