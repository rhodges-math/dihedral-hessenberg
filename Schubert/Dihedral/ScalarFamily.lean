import Schubert.Dihedral.IrreducibleFamily

/-! # Scalar-slot characters and their distinction -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral.ScalarFamily

/-- The fundamental rotation separates the first two and last two scalar slots. -/
theorem rotation_character (n : ℕ) [NeZero n]
    (index : Fin (if Even n then 4 else 2)) :
    (scalarFDRep n index).character (rotation n) = if index.val < 2 then 1 else -1 := by
  by_cases hzero : index.val = 0
  · rw [scalarFDRep, ite_eq_left hzero, FDRep.character_of_trivial]
    simp [hzero]
  · by_cases hone : index.val = 1
    · rw [scalarFDRep, ite_eq_right hzero, ite_eq_left hone, signFDRep_character,
        rotation_eq_r_one, signCharacter_r]
      simp [hone]
    · by_cases heven : Even n
      · rw [scalarFDRep, ite_eq_right hzero, ite_eq_right hone, dite_eq_left heven,
          evenScalarFDRep_character, evenScalarCharacter_rotation]
        have hnot : ¬ index.val < 2 := by omega
        simp only [hnot, ↓reduceIte]
      · have hbound := index.isLt
        simp only [heven, ↓reduceIte] at hbound
        omega

/-- The first simple reflection separates the even and odd scalar slots. -/
theorem s1_character (n : ℕ) [NeZero n]
    (index : Fin (if Even n then 4 else 2)) :
    (scalarFDRep n index).character (firstSimpleReflection n) =
      if index.val % 2 = 0 then 1 else -1 := by
  by_cases hzero : index.val = 0
  · rw [scalarFDRep, ite_eq_left hzero, FDRep.character_of_trivial]
    simp [hzero]
  · by_cases hone : index.val = 1
    · rw [scalarFDRep, ite_eq_right hzero, ite_eq_left hone, signFDRep_character]
      simp [firstSimpleReflection, signCharacter_sr, hone]
    · by_cases heven : Even n
      · rw [scalarFDRep, ite_eq_right hzero, ite_eq_right hone, dite_eq_left heven,
          evenScalarFDRep_character, evenScalarCharacter_s1]
        have hbound := index.isLt
        simp only [heven, ↓reduceIte] at hbound
        by_cases htwo : index.val = 2
        · simp [htwo]
        · have hthree : index.val = 3 := by omega
          simp [hthree]
      · have hbound := index.isLt
        simp only [heven, ↓reduceIte] at hbound
        omega

/-- All scalar slots have dimension one. -/
theorem finrank (n : ℕ) [NeZero n] (index : Fin (if Even n then 4 else 2)) :
    Module.finrank ℂ (scalarFDRep n index) = 1 := by
  by_cases hzero : index.val = 0
  · rw [scalarFDRep, ite_eq_left hzero]
    change Module.finrank ℂ ℂ = 1
    simp
  · by_cases hone : index.val = 1
    · rw [scalarFDRep, ite_eq_right hzero, ite_eq_left hone]
      exact signFDRep_finrank n
    · by_cases heven : Even n
      · rw [scalarFDRep, ite_eq_right hzero, ite_eq_right hone, dite_eq_left heven]
        exact evenScalarFDRep_finrank n heven _
      · rw [scalarFDRep, ite_eq_right hzero, ite_eq_right hone, dite_eq_right heven]
        change Module.finrank ℂ ℂ = 1
        simp

/-- Scalar slots are isomorphic exactly at equal indices. -/
theorem iso_iff_eq (n : ℕ) [NeZero n]
    (first second : Fin (if Even n then 4 else 2)) :
    Nonempty (scalarFDRep n first ≅ scalarFDRep n second) ↔ first = second := by
  constructor
  · rintro ⟨isomorphism⟩
    have hrotation := congrFun (FDRep.char_iso isomorphism) (rotation n)
    rw [rotation_character, rotation_character] at hrotation
    have hreflection := congrFun (FDRep.char_iso isomorphism) (firstSimpleReflection n)
    rw [s1_character, s1_character] at hreflection
    have hhalf : first.val < 2 ↔ second.val < 2 := by
      by_cases hfirst : first.val < 2
      · by_cases hsecond : second.val < 2
        · exact ⟨fun _ => hsecond, fun _ => hfirst⟩
        · simp only [hfirst, hsecond, ↓reduceIte] at hrotation
          norm_num at hrotation
      · by_cases hsecond : second.val < 2
        · simp only [hfirst, hsecond, ↓reduceIte] at hrotation
          norm_num at hrotation
        · exact ⟨fun h => (hfirst h).elim, fun h => (hsecond h).elim⟩
    have hparity : first.val % 2 = 0 ↔ second.val % 2 = 0 := by
      by_cases hfirst : first.val % 2 = 0
      · by_cases hsecond : second.val % 2 = 0
        · exact ⟨fun _ => hsecond, fun _ => hfirst⟩
        · simp only [hfirst, hsecond, ↓reduceIte] at hreflection
          norm_num at hreflection
      · by_cases hsecond : second.val % 2 = 0
        · simp only [hfirst, hsecond, ↓reduceIte] at hreflection
          norm_num at hreflection
        · exact ⟨fun h => (hfirst h).elim, fun h => (hsecond h).elim⟩
    have hcap : (if Even n then 4 else 2) ≤ 4 := by split_ifs <;> decide
    have hfirst := first.isLt
    have hsecond := second.isLt
    apply Fin.ext
    omega
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- No scalar slot is isomorphic to a frequency object of dimension two. -/
theorem not_frequency_iso (n : ℕ) [NeZero n]
    (index : Fin (if Even n then 4 else 2)) (frequency : ZMod n) :
    ¬ Nonempty (scalarFDRep n index ≅ frequencyFDRep n frequency) := by
  rintro ⟨isomorphism⟩
  have hdimension := congrFun (FDRep.char_iso isomorphism) (1 : DihedralGroup n)
  rw [FDRep.char_one, FDRep.char_one, finrank, frequencyFDRep_finrank] at hdimension
  norm_num at hdimension

end Schubert.Dihedral.ScalarFamily
