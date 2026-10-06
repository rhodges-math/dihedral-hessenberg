import Schubert.DihedralSplines.HexagonChamberObstruction
import Schubert.DihedralSplines.ChamberReflections

/-! # Sign choices in arbitrary six-root chambers -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private def sixNormals : Finset (PositiveRoot 6) := by
  classical
  exact {positiveRootEquiv 6 ⟨0, by decide⟩, positiveRootEquiv 6 ⟨1, by decide⟩,
    positiveRootEquiv 6 ⟨3, by decide⟩, positiveRootEquiv 6 ⟨4, by decide⟩}

/-- The unique positive signs of the four selected six-root directions in a generic chamber. -/
def sixChamberRoots (data : Separator 6) : Set RealPlane :=
  Subtype.val '' (data.choose '' (sixNormals : Set (PositiveRoot 6)))

/-- Every chamber sign choice retains exactly four vectors. -/
theorem six_chamber_card (data : Separator 6) : (sixChamberRoots data).ncard = 4 := by
  classical
  rw [sixChamberRoots, Set.ncard_image_of_injective _ Subtype.val_injective]
  change ((data.rootEquiv (by decide)) '' (sixNormals : Set (PositiveRoot 6))).ncard = 4
  rw [Set.ncard_image_of_injective _ (data.rootEquiv (by decide)).injective,
    Set.ncard_coe_finset]
  simp [sixNormals, (positiveRootEquiv 6).injective.eq_iff]

private theorem six_chamber_reflections (data : Separator 6) :
    (fun alpha : data.Positive => (data.reflectionEquiv (by decide) alpha).val) ''
      {alpha : data.Positive | alpha.val ∈ sixChamberRoots data} =
    {(positiveRootEquiv 6 ⟨0, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨1, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨3, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨4, by decide⟩).reflection} := by
  have hroots : {alpha : data.Positive | alpha.val ∈ sixChamberRoots data} =
      data.choose '' (sixNormals : Set (PositiveRoot 6)) :=
    Set.preimage_image_eq _ Subtype.val_injective
  rw [hroots, Set.image_image]
  simp only [data.reflection_choose]
  simp [sixNormals]

/-- The canonical chamber's sign selection is the four-vector subset. -/
theorem six_chamber_bisector :
    sixChamberRoots (Separator.bisector 6 (by decide)) = sixLowerRoots := by
  rw [sixChamberRoots, Set.image_image]
  simp only [Separator.choose_bisector]
  simp [sixNormals, sixLowerRoots]

/-- No generic chamber makes the four directions a cone ideal containing its simple pair. -/
theorem six_no_chamber_ideal (data : Separator 6) (frame : data.Frame)
    (hlower : ∀ alpha beta : data.Positive,
      (∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
        beta.val - alpha.val = first • (frame.first (by decide)).val +
          second • (frame.second (by decide)).val) →
      beta.val ∈ sixChamberRoots data → alpha.val ∈ sixChamberRoots data)
    (hfirst : (frame.first (by decide)).val ∈ sixChamberRoots data)
    (hsecond : (frame.second (by decide)).val ∈ sixChamberRoots data) : False := by
  have hpositive : sixChamberRoots data ⊆ data.positive := by
    rintro vector ⟨alpha, _, rfl⟩
    exact alpha.property
  obtain ⟨ideal, himage, hcard⟩ :=
    chamber_ideal frame (by decide) (sixChamberRoots data) hpositive hlower hfirst hsecond
  have hideal_card : ideal.carrier.ncard = 4 := hcard.symm.trans (six_chamber_card data)
  have hreflections := chamber_reflections frame (by decide) (sixChamberRoots data)
    ideal himage
  rw [six_chamber_reflections, six_four_reflections ideal hideal_card] at hreflections
  apply six_reflection_subset frame.element
  apply Finset.coe_injective
  rw [Finset.coe_image]
  simpa only [Finset.coe_insert, Finset.coe_singleton] using hreflections

end Schubert.DihedralSplines
