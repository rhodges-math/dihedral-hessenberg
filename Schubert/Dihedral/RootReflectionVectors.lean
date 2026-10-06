import Schubert.Dihedral.RootObjects
import Schubert.Dihedral.RootReflections

/-! # Positive vectors and canonical reflection carriers -/

noncomputable section

namespace Schubert.Dihedral

/-- Each positive vector defines a canonical Coxeter reflection. -/
theorem PositiveRoot.isReflection {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    (coxeterSystem n hthree).IsReflection alpha.reflection :=
  rootReflection_isReflection n hthree alpha.index

/-- Every canonical reflection is the reflection of a positive vector. -/
theorem isReflection_iff_positiveRoot (n : ℕ) (hthree : 3 ≤ n)
    (reflection : DihedralGroup n) :
    (coxeterSystem n hthree).IsReflection reflection ↔
      ∃ alpha : PositiveRoot n, alpha.reflection = reflection := by
  rw [isReflection_iff_exists_rootReflection]
  constructor
  · rintro ⟨index, hindex⟩
    exact ⟨positiveRootEquiv n index, (PositiveRoot.reflection_equiv n index).trans hindex⟩
  · rintro ⟨alpha, halpha⟩
    exact ⟨alpha.index, halpha⟩

/-- The positive root vectors are in bijection with the canonical reflection elements. -/
def positiveReflectionEquiv (n : ℕ) (hthree : 3 ≤ n) :
    PositiveRoot n ≃ {reflection : DihedralGroup n //
      (coxeterSystem n hthree).IsReflection reflection} :=
  Equiv.ofBijective (fun alpha => ⟨alpha.reflection, alpha.isReflection hthree⟩) (by
    constructor
    · intro alpha beta heq
      exact PositiveRoot.reflection_injective n (congrArg Subtype.val heq)
    · intro reflection
      obtain ⟨alpha, halpha⟩ :=
        (isReflection_iff_positiveRoot n hthree reflection.val).mp reflection.property
      exact ⟨alpha, Subtype.ext halpha⟩)

/-- Left multiplication by a root reflection descends exactly at a length decrease. -/
theorem PositiveRoot.bruhat_left {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (element : DihedralGroup n) :
    BruhatLE n hthree (alpha.reflection * element) element ↔
      length n hthree (alpha.reflection * element) < length n hthree element :=
  rootReflection_bruhatLE_mul_left_iff n hthree alpha.index element

/-- Right multiplication by a root reflection descends exactly at a length decrease. -/
theorem PositiveRoot.bruhat_right {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (element : DihedralGroup n) :
    BruhatLE n hthree (element * alpha.reflection) element ↔
      length n hthree (element * alpha.reflection) < length n hthree element :=
  rootReflection_bruhatLE_mul_right_iff n hthree alpha.index element

end Schubert.Dihedral
