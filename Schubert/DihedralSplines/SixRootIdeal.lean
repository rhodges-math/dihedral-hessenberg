import Schubert.DihedralSplines.ChamberRootOrder
import Schubert.Dihedral.HyperplanePullback
import Schubert.Dihedral.RootAngularEquality
import Schubert.DihedralSplines.HessenbergVectorClassification
import Mathlib.Tactic

/-! # A three-root ideal in a rotated hexagonal chamber -/

noncomputable section
namespace Schubert.DihedralSplines
open Schubert.Dihedral

private def sixSeparator : Separator 6 :=
  (Separator.bisector 6 (by decide)).pullback (.r 2)

private theorem six_cancel (vector : RealPlane) :
    realAction 6 (.r 2) (realAction 6 (.r 4) vector) = vector := by
  rw [← realAction_mul_plane, DihedralGroup.r_mul_r]
  change realAction 6 1 vector = vector
  rw [realAction_one]
  rfl

private theorem six_reverse_cancel (vector : RealPlane) :
    realAction 6 (.r 4) (realAction 6 (.r 2) vector) = vector := by
  rw [← realAction_mul_plane, DihedralGroup.r_mul_r]
  change realAction 6 1 vector = vector
  rw [realAction_one]
  rfl

private def sixFrame : sixSeparator.Frame where
  element := .r 4
  image := by
    ext vector
    constructor
    · intro hvector
      have hpositive : realAction 6 (.r 2) vector ∈
          (Separator.bisector 6 (by decide)).positive := by
        refine ⟨realAction_mem 6 _ vector hvector.1, ?_⟩
        exact ((Separator.bisector 6 (by decide)).transpose_pairing (.r 2) vector) ▸ hvector.2
      rw [Separator.positive_bisector] at hpositive
      exact ⟨realAction 6 (.r 2) vector, hpositive, six_reverse_cancel vector⟩
    · rintro ⟨alpha, halpha, rfl⟩
      refine ⟨realAction_mem 6 (.r 4) alpha (Or.inl halpha), ?_⟩
      change 0 < realBilinearForm (realAction 6 (.r 4) alpha)
        ((Separator.bisector 6 (by decide)).transposeNormal (.r 2))
      rw [Separator.transpose_pairing, six_cancel]
      exact ((Separator.positive_bisector 6 (by decide)).symm ▸ halpha).2

private theorem six_rotation_image (index image : Fin 6)
    (hangle : (angularIndex index + 8 : ℤ) % 12 = angularIndex image) :
    realAction 6 (.r 4) (positiveRoot 6 index) = positiveRoot 6 image := by
  apply complexify_injective
  rw [realAction_complexify 6 _ _ (Or.inl ⟨index, rfl⟩)]
  change vectorOperator 6 (.r 4) (complexPositiveRoot 6 index) = _
  rw [vectorOperator_r_complexPositiveRoot]
  apply congrArg complexify
  change unitRootAt (((angularIndex index + 8 : ℕ) : ℝ) * Real.pi / (6 : ℕ)) = _
  have hroot := (unitRootAt_int_eq_positiveRoot_iff 6 (angularIndex index + 8) image).mpr hangle
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_ofNat] using hroot

private theorem six_rotation_negative (index image : Fin 6)
    (hangle : (angularIndex index + 8 : ℤ) % 12 = angularIndex image + 6) :
    realAction 6 (.r 4) (positiveRoot 6 index) = -positiveRoot 6 image := by
  apply complexify_injective
  rw [realAction_complexify 6 _ _ (Or.inl ⟨index, rfl⟩)]
  change vectorOperator 6 (.r 4) (complexPositiveRoot 6 index) = _
  rw [vectorOperator_r_complexPositiveRoot]
  apply congrArg complexify
  change unitRootAt (((angularIndex index + 8 : ℕ) : ℝ) * Real.pi / (6 : ℕ)) = _
  have hroot : unitRootAt (((angularIndex index + 8 : ℤ) : ℝ) * Real.pi / (6 : ℕ)) =
      -positiveRoot 6 image := by
    rw [unitRootAt_int_eq_emod]
    norm_num only [Nat.cast_ofNat, Int.reduceMul]
    rw [hangle, positiveRoot, rootAngle_eq_angularIndex, ← unitRootAt_add_pi]
    congr 1
    push_cast
    ring
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_ofNat] using hroot

/-- The two simple vectors are exactly the declared signed pair. -/
private theorem six_resimple_pair :
    (sixFrame.first (by decide)).val = -positiveRoot 6 4 ∧
    (sixFrame.second (by decide)).val = positiveRoot 6 2 := by
  constructor
  · change realAction 6 (.r 4) (simpleRoot 6 (by decide) 0).val = _
    rw [simpleRoot_zero, positiveRootEquiv_val]
    exact six_rotation_negative _ _ (by decide)
  · change realAction 6 (.r 4) (simpleRoot 6 (by decide) 1).val = _
    rw [simpleRoot_one, positiveRootEquiv_val]
    exact six_rotation_image _ _ (by decide)

private theorem six_positive : sixSeparator.positive =
    {positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4, -positiveRoot 6 5,
      -positiveRoot 6 3, -positiveRoot 6 1} := by
  have hindices : (Set.univ : Set (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
    ext index
    fin_cases index <;> decide
  have hcanonical : positiveRoots 6 = positiveRoot 6 '' (Set.univ : Set (Fin 6)) := by
    ext vector
    simp [positiveRoots]
  have h0 := six_rotation_negative 0 4 (by decide)
  have h1 := six_rotation_image 1 2 (by decide)
  have h2 := six_rotation_negative 2 5 (by decide)
  have h3 := six_rotation_image 3 0 (by decide)
  have h4 := six_rotation_negative 4 3 (by decide)
  have h5 := six_rotation_negative 5 1 (by decide)
  rw [sixFrame.image, hcanonical, hindices]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change {realAction 6 (.r 4) (positiveRoot 6 0),
    realAction 6 (.r 4) (positiveRoot 6 1), realAction 6 (.r 4) (positiveRoot 6 2),
    realAction 6 (.r 4) (positiveRoot 6 3), realAction 6 (.r 4) (positiveRoot 6 4),
    realAction 6 (.r 4) (positiveRoot 6 5)} = _
  rw [h0, h1, h2, h3, h4, h5]
  ext vector
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The signed three-root set is a lower cone ideal for the declared simple pair. -/
theorem six_three_root_ideal :
    ∃ data : Separator 6, ∃ frame : data.Frame,
      (frame.first (by decide)).val = -positiveRoot 6 4 ∧
      (frame.second (by decide)).val = positiveRoot 6 2 ∧
      data.positive = {positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4,
        -positiveRoot 6 5, -positiveRoot 6 3, -positiveRoot 6 1} ∧
      ({positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4} : Set RealPlane).ncard = 3 ∧
      {positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4} ⊆ data.positive ∧
      ∀ alpha beta : data.Positive,
        (∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
          beta.val - alpha.val = first • (frame.first (by decide)).val +
            second • (frame.second (by decide)).val) →
        beta.val ∈ ({positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4} : Set RealPlane) →
        alpha.val ∈ ({positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4} : Set RealPlane) := by
  obtain ⟨ideal, hcard, hcarrier⟩ := HessenbergIdeal.exists_other 6 (by decide) 2
    (by decide) (by decide)
  have hindices : {index : Fin 6 | index.val < 2 * 2 - 2 ∨ index.val = 2 * 2 - 1} =
      {0, 1, 3} := by
    ext index
    fin_cases index <;> decide
  rw [hindices, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at hcarrier
  have h0 := six_rotation_negative 0 4 (by decide)
  have h1 := six_rotation_image 1 2 (by decide)
  have h3 := six_rotation_image 3 0 (by decide)
  have himage : realAction 6 (.r 4) '' ideal.carrier =
      {positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4} := by
    rw [hcarrier, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, h0, h1, h3]
    ext vector
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hselectedCard :
      ({positiveRoot 6 0, positiveRoot 6 2, -positiveRoot 6 4} : Set RealPlane).ncard = 3 := by
    have hinjective : Function.Injective (realAction 6 (.r 4)) :=
      (realLinearEquiv 6 (.r 4)).injective
    rw [← himage, Set.ncard_image_of_injective _ hinjective]
    simpa using hcard
  refine ⟨sixSeparator, sixFrame, six_resimple_pair.1, six_resimple_pair.2,
    six_positive, hselectedCard, ?_, ?_⟩
  · intro vector hvector
    rw [← himage] at hvector
    obtain ⟨root, hroot, rfl⟩ := hvector
    rw [sixFrame.image]
    exact ⟨root, ideal.positive hroot, rfl⟩
  · have hsurj : Function.Surjective sixFrame.root := by
      intro alpha
      have hpositive : alpha.val ∈ realAction 6 sixFrame.element '' positiveRoots 6 :=
        Eq.mp (congrArg (fun carrier : Set RealPlane => alpha.val ∈ carrier)
          sixFrame.image) alpha.property
      obtain ⟨root, hroot, heq⟩ := hpositive
      exact ⟨⟨root, hroot⟩, Subtype.ext heq⟩
    intro alpha beta hcone hbeta
    obtain ⟨first, rfl⟩ := hsurj alpha
    obtain ⟨second, rfl⟩ := hsurj beta
    have horder := (chamber_order sixFrame (by decide) first second).mp hcone
    have hsecond : second.val ∈ ideal.carrier := by
      rw [← himage] at hbeta
      obtain ⟨root, hroot, heq⟩ := hbeta
      have hequal := (realLinearEquiv 6 (.r 4)).injective heq
      exact hequal ▸ hroot
    rw [← himage]
    exact ⟨first.val, ideal.lower horder hsecond, rfl⟩

end Schubert.DihedralSplines
