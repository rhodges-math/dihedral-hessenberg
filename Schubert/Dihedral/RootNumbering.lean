import Schubert.Dihedral.RootObjects

/-! # Alternating reflection words for numbered root vectors -/

namespace Schubert.Dihedral

/-- Odd one-based numbered root vectors have the alternating word beginning with s1. -/
theorem numbered_even_reflection (n exponent : ℕ) (hbound : 2 * exponent < n) :
    (positiveRootEquiv n ⟨2 * exponent, hbound⟩).reflection =
      (firstSimpleReflection n * secondSimpleReflection n) ^ exponent *
        firstSimpleReflection n := by
  rw [PositiveRoot.reflection_equiv, rootReflection_of_even_index _ (by simp)]
  have hquotient : 2 * exponent / 2 = exponent := by omega
  change rotation n ^ (2 * exponent / 2) * firstSimpleReflection n = _
  rw [hquotient]
  rfl

/-- Even one-based numbered root vectors have the alternating word beginning with s2. -/
theorem numbered_odd_reflection (n exponent : ℕ) (hbound : 2 * exponent + 1 < n) :
    (positiveRootEquiv n ⟨2 * exponent + 1, hbound⟩).reflection =
      (secondSimpleReflection n * firstSimpleReflection n) ^ exponent *
        secondSimpleReflection n := by
  rw [PositiveRoot.reflection_equiv, rootReflection_of_odd_index _ (by simp)]
  have hquotient : (2 * exponent + 1) / 2 = exponent := by omega
  change (secondSimpleReflection n * firstSimpleReflection n) ^
    ((2 * exponent + 1) / 2) * secondSimpleReflection n = _
  rw [hquotient]

end Schubert.Dihedral
