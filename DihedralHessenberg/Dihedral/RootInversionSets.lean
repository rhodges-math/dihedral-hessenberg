import DihedralHessenberg.Dihedral.RootSubset
import DihedralHessenberg.Dihedral.RootInversionSigns
import DihedralHessenberg.Dihedral.Inversions
import Mathlib.Data.Set.Card

/-! # Geometric inversion sets of positive vectors -/

noncomputable section

namespace Schubert.Dihedral

/-- Positive vectors sent to negative roots by the inverse action. -/
def leftInversionSet (n : ℕ) (element : DihedralGroup n) : Set RealPlane :=
  {alpha | alpha ∈ positiveRoots n ∧ -realAction n element⁻¹ alpha ∈ positiveRoots n}

/-- Positive vectors sent to negative roots by the action. -/
def rightInversionSet (n : ℕ) (element : DihedralGroup n) : Set RealPlane :=
  {alpha | alpha ∈ positiveRoots n ∧ -realAction n element alpha ∈ positiveRoots n}

/-- Alternating numbering preserves right inversion membership. -/
theorem mem_rightInversionSet (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    positiveRoot n index ∈ rightInversionSet n element ↔
      index ∈ rightInversions n hthree element := by
  change (positiveRoot n index ∈ positiveRoots n ∧
    -(fun coordinate =>
      (vectorOperator n element (complexPositiveRoot n index) coordinate).re) ∈
        positiveRoots n) ↔ _
  rw [and_iff_right (show positiveRoot n index ∈ positiveRoots n from ⟨index, rfl⟩)]
  exact (mem_rightInversions_iff_negative_image n hthree element index).symm

/-- Alternating numbering preserves left inversion membership. -/
theorem mem_leftInversionSet (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    positiveRoot n index ∈ leftInversionSet n element ↔
      index ∈ leftInversions n hthree element := by
  change positiveRoot n index ∈ rightInversionSet n element⁻¹ ↔ _
  rw [mem_rightInversionSet, rightInversions_inv_eq_leftInversions]

/-- The right inversion set is exactly the vector image of canonical right inversions. -/
theorem image_rightInversions (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    positiveRoot n '' (rightInversions n hthree element : Set (PositiveRootIndex n)) =
      rightInversionSet n element := by
  ext alpha
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact (mem_rightInversionSet n hthree element index).mpr hindex
  · intro hmem
    obtain ⟨index, rfl⟩ := hmem.1
    exact ⟨index, (mem_rightInversionSet n hthree element index).mp hmem, rfl⟩

/-- The left inversion set is exactly the vector image of canonical left inversions. -/
theorem image_leftInversions (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    positiveRoot n '' (leftInversions n hthree element : Set (PositiveRootIndex n)) =
      leftInversionSet n element := by
  change _ = rightInversionSet n element⁻¹
  rw [← image_rightInversions n hthree element⁻¹, rightInversions_inv_eq_leftInversions]

namespace RootSubset

/-- The selected positive vectors whose images are negative. -/
def inversions {n : ℕ} (selected : RootSubset n) (element : DihedralGroup n) : Set RealPlane :=
  selected.carrier ∩ rightInversionSet n element

/-- The number of selected positive vectors whose images are negative. -/
def length {n : ℕ} (selected : RootSubset n) (element : DihedralGroup n) : ℕ :=
  (selected.inversions element).ncard

/-- Selected inversion membership consists of selection and a negative image. -/
theorem mem_inversions {n : ℕ} (selected : RootSubset n) (element : DihedralGroup n)
    (alpha : RealPlane) :
    alpha ∈ selected.inversions element ↔
      alpha ∈ selected ∧ -realAction n element alpha ∈ positiveRoots n := by
  constructor
  · exact fun hmem => ⟨hmem.1, hmem.2.2⟩
  · exact fun hmem => ⟨hmem.1, selected.positive hmem.1, hmem.2⟩

/-- Every selected inversion set is finite. -/
theorem inversions_finite {n : ℕ} (selected : RootSubset n) (element : DihedralGroup n) :
    (selected.inversions element).Finite := selected.finite.subset Set.inter_subset_left

end RootSubset

end Schubert.Dihedral
