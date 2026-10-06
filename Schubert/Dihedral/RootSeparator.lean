import Schubert.Dihedral.RootHalfspace
import Schubert.Dihedral.RootReflectionVectors
import Schubert.Dihedral.RootRescaling

/-! # Generic separating hyperplanes for the signed unit roots -/

noncomputable section

namespace Schubert.Dihedral

/-- A normal vector whose hyperplane contains no signed root. -/
structure Separator (n : ℕ) where
  /-- The real normal vector. -/
  normal : RealPlane
  /-- Every signed root pairs nontrivially with the normal. -/
  generic : ∀ vector ∈ roots n, realBilinearForm vector normal ≠ 0

namespace Separator

variable {n : ℕ}

/-- The root vectors on the positive side of the separating hyperplane. -/
def positive (data : Separator n) : Set RealPlane :=
  {vector ∈ roots n | 0 < realBilinearForm vector data.normal}

/-- Positive roots for the chosen separating hyperplane. -/
abbrev Positive (data : Separator n) := {vector // vector ∈ data.positive}

/-- The signed roots partition into the two open sides of any generic hyperplane. -/
theorem partition (data : Separator n) :
    roots n = data.positive ∪ {vector | -vector ∈ data.positive} := by
  ext vector
  constructor
  · intro hroot
    by_cases hpos : 0 < realBilinearForm vector data.normal
    · exact Or.inl ⟨hroot, hpos⟩
    · refine Or.inr ⟨(roots_neg_iff n vector).mpr hroot, ?_⟩
      simp only [realBilinearForm, Pi.neg_apply, neg_mul]
      have hnonzero := data.generic vector hroot
      change vector 0 * data.normal 0 + vector 1 * data.normal 1 ≠ 0 at hnonzero
      change ¬0 < vector 0 * data.normal 0 + vector 1 * data.normal 1 at hpos
      have hnegative := lt_of_le_of_ne (le_of_not_gt hpos) hnonzero
      linarith
  · rintro (hpos | hneg)
    · exact hpos.1
    · exact (roots_neg_iff n vector).mp hneg.1

/-- The two open sides of the separator contain no common root. -/
theorem disjoint (data : Separator n) :
    Disjoint data.positive {vector | -vector ∈ data.positive} := by
  rw [Set.disjoint_left]
  intro vector hpos hneg
  have hp := hpos.2
  have hn := hneg.2
  simp only [realBilinearForm, Pi.neg_apply, neg_mul] at hp hn
  linarith

/-- Choose the signed representative on the positive side of a generic hyperplane. -/
def choose (data : Separator n) (alpha : PositiveRoot n) : data.Positive :=
  if hpos : 0 < realBilinearForm alpha.val data.normal then
    ⟨alpha.val, Or.inl alpha.property, hpos⟩
  else
    ⟨-alpha.val, (roots_neg_iff n alpha.val).mpr (Or.inl alpha.property), by
      have hnonzero := data.generic alpha.val (Or.inl alpha.property)
      simp only [realBilinearForm, Pi.neg_apply, neg_mul]
      change alpha.val 0 * data.normal 0 + alpha.val 1 * data.normal 1 ≠ 0 at hnonzero
      change ¬0 < alpha.val 0 * data.normal 0 + alpha.val 1 * data.normal 1 at hpos
      have hnegative := lt_of_le_of_ne (le_of_not_gt hpos) hnonzero
      linarith⟩

private theorem positive_ne_negative (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) :
    alpha.val ≠ -beta.val := by
  intro heq
  have ha := alpha.halfspace_pos hthree
  have hb := beta.halfspace_pos hthree
  rw [heq] at ha
  simp only [realBilinearForm, Pi.neg_apply, neg_mul] at ha hb
  linarith

/-- Sign choice bijectively identifies the canonical roots with any generic positive side. -/
def rootEquiv (data : Separator n) (hthree : 3 ≤ n) : PositiveRoot n ≃ data.Positive :=
  Equiv.ofBijective data.choose (by
    constructor
    · intro alpha beta heq
      have hv := congrArg Subtype.val heq
      unfold choose at hv
      split_ifs at hv with ha hb
      · exact Subtype.ext hv
      · exact False.elim (positive_ne_negative hthree alpha beta hv)
      · exact False.elim (positive_ne_negative hthree beta alpha hv.symm)
      · exact Subtype.ext (neg_injective hv)
    · intro vector
      rcases vector.property.1 with hpositive | hnegative
      · refine ⟨⟨vector.val, hpositive⟩, ?_⟩
        apply Subtype.ext
        simp only [choose, dite_eq_left vector.property.2]
      · refine ⟨⟨-vector.val, hnegative⟩, ?_⟩
        have hn : ¬0 < realBilinearForm (-vector.val) data.normal := by
          have hp := vector.property.2
          simp only [realBilinearForm, Pi.neg_apply, neg_mul] at hp ⊢
          linarith
        apply Subtype.ext
        simp only [choose, dite_eq_right hn, neg_neg])

/-- Roots on any generic positive side correspond bijectively to Coxeter reflections. -/
def reflectionEquiv (data : Separator n) (hthree : 3 ≤ n) :
    data.Positive ≃ {element : DihedralGroup n //
      (coxeterSystem n hthree).IsReflection element} :=
  (data.rootEquiv hthree).symm.trans (positiveReflectionEquiv n hthree)

/-- Sign choice does not change the corresponding reflection. -/
theorem reflection_choose (data : Separator n) (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    (data.reflectionEquiv hthree (data.choose alpha)).val = alpha.reflection := by
  change ((positiveReflectionEquiv n hthree)
    ((data.rootEquiv hthree).symm ((data.rootEquiv hthree) alpha))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The reflection associated to a generic positive root has its normal formula. -/
theorem reflection_apply (data : Separator n) (hthree : 3 ≤ n) (alpha : data.Positive)
    (vector : RealPlane) :
    realAction n (data.reflectionEquiv hthree alpha).val vector =
      vector - (2 * realBilinearForm vector alpha.val /
        realBilinearForm alpha.val alpha.val) • alpha.val := by
  let beta := (data.rootEquiv hthree).symm alpha
  have hchoose : data.choose beta = alpha := (data.rootEquiv hthree).apply_symm_apply alpha
  rw [← hchoose, reflection_choose]
  unfold choose
  split_ifs
  · simpa only [one_smul] using
      (beta.scaled_reflection 1 one_ne_zero vector).symm
  · simpa only [neg_one_smul] using
      (beta.scaled_reflection (-1) (by norm_num) vector).symm

/-- The canonical simple-root bisector defines a generic separator. -/
def bisector (n : ℕ) (hthree : 3 ≤ n) : Separator n where
  normal := (simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val
  generic := roots_halfspace_nonzero n hthree

/-- The bisector's positive side is exactly the chosen canonical positive root set. -/
theorem positive_bisector (n : ℕ) (hthree : 3 ≤ n) :
    (bisector n hthree).positive = positiveRoots n :=
  (positiveRoots_halfspace n hthree).symm

/-- The canonical separator retains every canonical root vector with its sign unchanged. -/
theorem choose_bisector (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    ((bisector n hthree).choose alpha).val = alpha.val := by
  unfold choose bisector
  rw [dite_eq_left (alpha.halfspace_pos hthree)]

end Separator
end Schubert.Dihedral
