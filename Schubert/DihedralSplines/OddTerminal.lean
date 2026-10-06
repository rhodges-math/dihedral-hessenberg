import Schubert.DihedralSplines.DominanceEven
import Schubert.Dihedral.ConjugatedLength

/-! # The selected terminal vector of an odd ideal -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- An odd ideal selects exactly one vector from its final alternating layer. -/
theorem terminal_choice (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hbound : 2 * half + 1 < n) :
    (positiveRootEquiv n ⟨2 * half, by omega⟩).val ∈ ideal ↔
      (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).val ∉ ideal := by
  have hindexed : ideal.indexed.roots.card = 2 * half + 1 := by
    rw [← ideal.ncard_indexed, hcard]
  change positiveRoot n ⟨2 * half, _⟩ ∈ ideal ↔ positiveRoot n ⟨2 * half + 1, _⟩ ∉ ideal
  rw [← ideal.mem_indexed, ← ideal.mem_indexed]
  rcases ideal.indexed.root_membership_classification with hprefix | ⟨_, _, hother⟩
  · rw [hprefix, hprefix, hindexed]
    change 2 * half < 2 * half + 1 ↔ ¬2 * half + 1 < 2 * half + 1
    omega
  · rw [hother, hother, hindexed]
    change (2 * half < 2 * half + 1 - 1 ∨ 2 * half = 2 * half + 1) ↔
      ¬(2 * half + 1 < 2 * half + 1 - 1 ∨ 2 * half + 1 = 2 * half + 1)
    omega

/-- Two selected vectors at the full odd ideal length are the same terminal vector. -/
theorem terminal_unique (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (alpha beta : PositiveRoot n)
    (halpha : alpha.val ∈ ideal) (hbeta : beta.val ∈ ideal)
    (hfirst : length n hthree alpha.reflection = ideal.carrier.ncard)
    (hsecond : length n hthree beta.reflection = ideal.carrier.ncard) : alpha = beta := by
  have hindexed : ideal.indexed.roots.card = 2 * half + 1 := by
    rw [← ideal.ncard_indexed, hcard]
  have hmemFirst : alpha.index ∈ ideal.indexed.roots := by
    rw [ideal.mem_indexed, PositiveRoot.index_val]
    exact halpha
  have hmemSecond : beta.index ∈ ideal.indexed.roots := by
    rw [ideal.mem_indexed, PositiveRoot.index_val]
    exact hbeta
  change length n hthree (rootReflection alpha.index) = ideal.carrier.ncard at hfirst
  change length n hthree (rootReflection beta.index) = ideal.carrier.ncard at hsecond
  rw [length_rootReflection, hcard] at hfirst hsecond
  apply (positiveRootEquiv n).symm.injective
  apply Fin.ext
  change alpha.index.val = beta.index.val
  rcases ideal.indexed.root_membership_classification with hprefix | ⟨_, _, hother⟩
  · have hfirstBound := (hprefix alpha.index).mp hmemFirst
    have hsecondBound := (hprefix beta.index).mp hmemSecond
    rw [hindexed] at hfirstBound hsecondBound
    omega
  · have hfirstBound := (hother alpha.index).mp hmemFirst
    have hsecondBound := (hother beta.index).mp hmemSecond
    rw [hindexed] at hfirstBound hsecondBound
    omega

end Schubert.DihedralSplines.HessenbergIdeal
