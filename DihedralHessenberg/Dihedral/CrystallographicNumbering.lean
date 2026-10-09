import DihedralHessenberg.Dihedral.RootClassRadius
import DihedralHessenberg.Dihedral.RootLattice

/-! # Intrinsic radial identifications of rank-two positive configurations -/

namespace Schubert.Dihedral.RootLattice

/-- Conjugacy-class rescaling produces the six numbered G positive vectors. -/
theorem g2_numbered (index : PositiveRootIndex 6) :
    PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 index) •
        positiveRoot 6 index =
      ![g2.first, g2.second, (3 : ℝ) • g2.first + g2.second, g2.first + g2.second,
        (2 : ℝ) • g2.first + g2.second, (3 : ℝ) • g2.first + (2 : ℝ) • g2.second] index := by
  have htwo : Real.pi / 6 + Real.pi / 6 = Real.pi / 3 := by ring
  have hthird : (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 := by ring
  have hhalf : Real.pi / 3 + Real.pi / 6 = Real.pi / 2 := by ring
  have hsquare : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hratio : Real.sqrt 3 / 2 / (1 / 2) = Real.sqrt 3 := by ring
  have hprod : Real.sqrt 3 * (Real.sqrt 3 / 2 / (1 / 2)) = 3 := by rw [hratio, hsquare]
  rw [PositiveRoot.classRadius_six, positiveRoot_eq_rootConeCoordinates 6 (by decide)]
  fin_cases index
  all_goals first
    | rw [rootConeCoordinates_of_even 6 _ (by decide)]
    | rw [rootConeCoordinates_of_odd 6 (by decide) _ (by decide)]
  all_goals norm_num [htwo, hthird, hhalf, Real.sin_pi_div_six, Real.sin_pi_div_three,
    g2, simpleRoot_zero, simpleRoot_one, positiveRootEquiv_val, Nat.cast_ofNat,
    smul_add, smul_smul, hsquare, hratio, hprod]
  all_goals (congr 1; ring)

/-- The intrinsic conjugacy-class rescaling has exactly the G positive-vector carrier. -/
theorem g2_image : g2.positive =
    Set.range (fun alpha : PositiveRoot 6 =>
      PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) alpha • alpha.val) := by
  have hset : g2.positive = {g2.first, g2.second, g2.first + g2.second,
      (2 : ℝ) • g2.first + g2.second, (3 : ℝ) • g2.first + g2.second,
      (3 : ℝ) • g2.first + (2 : ℝ) • g2.second} := rfl
  rw [hset]
  ext vector
  constructor
  · intro hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨positiveRootEquiv 6 ⟨0, by decide⟩, by simpa using g2_numbered ⟨0, by decide⟩⟩
    · exact ⟨positiveRootEquiv 6 ⟨1, by decide⟩, by simpa using g2_numbered ⟨1, by decide⟩⟩
    · exact ⟨positiveRootEquiv 6 ⟨3, by decide⟩, by simpa using g2_numbered ⟨3, by decide⟩⟩
    · exact ⟨positiveRootEquiv 6 ⟨4, by decide⟩, by simpa using g2_numbered ⟨4, by decide⟩⟩
    · exact ⟨positiveRootEquiv 6 ⟨2, by decide⟩, by simpa using g2_numbered ⟨2, by decide⟩⟩
    · exact ⟨positiveRootEquiv 6 ⟨5, by decide⟩, by simpa using g2_numbered ⟨5, by decide⟩⟩
  · rintro ⟨alpha, rfl⟩
    obtain ⟨index, rfl⟩ := (positiveRootEquiv 6).surjective alpha
    change PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 index) •
      positiveRoot 6 index ∈ _
    rw [g2_numbered]
    fin_cases index <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals tauto

/-- Conjugacy-class rescaling produces the four numbered B2 positive vectors. -/
theorem b2_numbered (index : PositiveRootIndex 4) :
    PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 index) •
        positiveRoot 4 index =
          ![b2.first, b2.second, (2 : ℝ) • b2.first + b2.second, b2.first + b2.second] index := by
  have htwo : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by ring
  have hsquare : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 / 2 ≠ 0 := by positivity
  have hratio : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
    field_simp
    nlinarith
  have hprod : Real.sqrt 2 * (1 / (Real.sqrt 2 / 2)) = 2 := by rw [hratio, hsquare]
  rw [PositiveRoot.classRadius_four, positiveRoot_eq_rootConeCoordinates 4 (by decide)]
  fin_cases index
  all_goals first
    | rw [rootConeCoordinates_of_even 4 _ (by decide)]
    | rw [rootConeCoordinates_of_odd 4 (by decide) _ (by decide)]
  all_goals norm_num [htwo, Real.sin_pi_div_four, b2, simpleRoot_zero, simpleRoot_one,
    positiveRootEquiv_val, Nat.cast_ofNat, smul_add, smul_smul, hsquare, hne, hratio, hprod]

/-- Conjugacy-class rescaling produces the four numbered C2 positive vectors. -/
theorem c2_numbered (index : PositiveRootIndex 4) :
    PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 index) •
        positiveRoot 4 index =
          ![c2.first, c2.second, c2.first + c2.second, c2.first + (2 : ℝ) • c2.second] index := by
  have htwo : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by ring
  have hsquare : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 / 2 ≠ 0 := by positivity
  have hratio : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
    field_simp
    nlinarith
  have hprod : Real.sqrt 2 * (1 / (Real.sqrt 2 / 2)) = 2 := by rw [hratio, hsquare]
  rw [PositiveRoot.classRadius_four, positiveRoot_eq_rootConeCoordinates 4 (by decide)]
  fin_cases index
  all_goals first
    | rw [rootConeCoordinates_of_even 4 _ (by decide)]
    | rw [rootConeCoordinates_of_odd 4 (by decide) _ (by decide)]
  all_goals norm_num [htwo, Real.sin_pi_div_four, c2, simpleRoot_zero, simpleRoot_one,
    positiveRootEquiv_val, Nat.cast_ofNat, smul_add, smul_smul, hsquare, hne, hratio, hprod]

/-- The intrinsic class rescaling has exactly the B2 positive-vector carrier. -/
theorem b2_image : b2.positive =
    Set.range (fun alpha : PositiveRoot 4 =>
      PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) alpha • alpha.val) := by
  have hset : b2.positive =
      {b2.first, b2.second, b2.first + b2.second, (2 : ℝ) • b2.first + b2.second} := rfl
  rw [hset]
  ext vector
  constructor
  · intro hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact ⟨positiveRootEquiv 4 ⟨0, by decide⟩, by simpa using b2_numbered ⟨0, by decide⟩⟩
    · exact ⟨positiveRootEquiv 4 ⟨1, by decide⟩, by simpa using b2_numbered ⟨1, by decide⟩⟩
    · exact ⟨positiveRootEquiv 4 ⟨3, by decide⟩, by simpa using b2_numbered ⟨3, by decide⟩⟩
    · exact ⟨positiveRootEquiv 4 ⟨2, by decide⟩, by simpa using b2_numbered ⟨2, by decide⟩⟩
  · rintro ⟨alpha, rfl⟩
    obtain ⟨index, rfl⟩ := (positiveRootEquiv 4).surjective alpha
    change PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 index) •
      positiveRoot 4 index ∈ _
    rw [b2_numbered]
    fin_cases index <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals tauto

/-- The intrinsic class rescaling has exactly the C2 positive-vector carrier. -/
theorem c2_image : c2.positive =
    Set.range (fun alpha : PositiveRoot 4 =>
      PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 alpha • alpha.val) := by
  have hset : c2.positive =
      {c2.first, c2.second, c2.first + c2.second, c2.first + (2 : ℝ) • c2.second} := rfl
  rw [hset]
  ext vector
  constructor
  · intro hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact ⟨positiveRootEquiv 4 ⟨0, by decide⟩, by simpa using c2_numbered ⟨0, by decide⟩⟩
    · exact ⟨positiveRootEquiv 4 ⟨1, by decide⟩, by simpa using c2_numbered ⟨1, by decide⟩⟩
    · exact ⟨positiveRootEquiv 4 ⟨2, by decide⟩, by simpa using c2_numbered ⟨2, by decide⟩⟩
    · exact ⟨positiveRootEquiv 4 ⟨3, by decide⟩, by simpa using c2_numbered ⟨3, by decide⟩⟩
  · rintro ⟨alpha, rfl⟩
    obtain ⟨index, rfl⟩ := (positiveRootEquiv 4).surjective alpha
    change PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 index) •
      positiveRoot 4 index ∈ _
    rw [c2_numbered]
    fin_cases index <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals tauto

end Schubert.Dihedral.RootLattice
