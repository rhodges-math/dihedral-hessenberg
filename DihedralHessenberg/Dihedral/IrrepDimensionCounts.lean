import DihedralHessenberg.Dihedral.IrreducibleClassification

/-! # Dimension counts in the complete dihedral irreducible family -/

noncomputable section

namespace Schubert.Dihedral

/-- The scalar and frequency slots have dimensions one and two respectively. -/
theorem irrepFDRep_finrank (n : ℕ) [NeZero n] (index : IrrepIndex n) :
    Module.finrank ℂ (irrepFDRep n index) = Sum.elim (fun _ => 1) (fun _ => 2) index := by
  cases index with
  | inl scalar => exact ScalarFamily.finrank n scalar
  | inr frequency => exact frequencyFDRep_finrank n (frequency.val + 1 : ℕ)

/-- The complete nonisomorphic family has exactly two or four one-dimensional members. -/
theorem irrep_count_one (n : ℕ) [NeZero n] :
    Fintype.card {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 1} =
      if Even n then 4 else 2 := by
  let equivalence :
      {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 1} ≃
        Fin (if Even n then 4 else 2) :=
    { toFun := by
        rintro ⟨index, hdimension⟩
        cases index with
        | inl scalar => exact scalar
        | inr frequency => rw [irrepFDRep_finrank] at hdimension; simp at hdimension
      invFun := fun scalar => ⟨.inl scalar, ScalarFamily.finrank n scalar⟩
      left_inv := by
        rintro ⟨index, hdimension⟩
        cases index with
        | inl scalar => rfl
        | inr frequency => rw [irrepFDRep_finrank] at hdimension; simp at hdimension
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr equivalence).trans (Fintype.card_fin _)

/-- The complete nonisomorphic family has one two-dimensional member per lower-half frequency. -/
theorem irrep_count_two (n : ℕ) [NeZero n] :
    Fintype.card {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 2} =
      (n - 1) / 2 := by
  let equivalence :
      {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 2} ≃
        Fin ((n - 1) / 2) :=
    { toFun := by
        rintro ⟨index, hdimension⟩
        cases index with
        | inl scalar => rw [irrepFDRep_finrank] at hdimension; simp at hdimension
        | inr frequency => exact frequency
      invFun := fun frequency => ⟨.inr frequency, frequencyFDRep_finrank n _⟩
      left_inv := by
        rintro ⟨index, hdimension⟩
        cases index with
        | inl scalar => rw [irrepFDRep_finrank] at hdimension; simp at hdimension
        | inr frequency => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr equivalence).trans (Fintype.card_fin _)

/-- Odd rotation order gives the exact two scalar and lower-half frequency counts. -/
theorem irrep_counts_odd (n : ℕ) [NeZero n] (hodd : Odd n) :
    Fintype.card {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 1} = 2 ∧
      Fintype.card {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 2} =
        (n - 1) / 2 := by
  simp only [irrep_count_one, irrep_count_two, Nat.not_even_iff_odd.mpr hodd, ite_false, and_self]

/-- Even rotation order gives four scalar and exactly (n−2)/2 two-dimensional members. -/
theorem irrep_counts_even (n : ℕ) [NeZero n] (heven : Even n) :
    Fintype.card {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 1} = 4 ∧
      Fintype.card {index : IrrepIndex n // Module.finrank ℂ (irrepFDRep n index) = 2} =
        (n - 2) / 2 := by
  constructor
  · simpa only [heven, ite_true] using irrep_count_one n
  · rw [irrep_count_two]
    obtain ⟨half, hhalf⟩ := heven
    have hpositive := NeZero.pos n
    omega

end Schubert.Dihedral
