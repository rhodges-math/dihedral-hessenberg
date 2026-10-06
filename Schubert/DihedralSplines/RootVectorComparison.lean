import Schubert.DihedralSplines.HessenbergVectorClassification
import Schubert.Dihedral.RankTwoBruhat
import Schubert.Dihedral.AlternatingWords

/-! # Strict cone, reflection-length and Bruhat comparisons of root vectors -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Strict real-cone comparison is strict length comparison of the corresponding reflections. -/
theorem rootOrder_length {n : ℕ} (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) :
    (RootOrder n hthree alpha beta ∧ alpha ≠ beta) ↔
      length n hthree alpha.reflection < length n hthree beta.reflection := by
  rw [rootOrder_layers]
  change ((alpha = beta ∨ alpha.index.val / 2 < beta.index.val / 2) ∧ alpha ≠ beta) ↔
    length n hthree (rootReflection alpha.index) < length n hthree (rootReflection beta.index)
  rw [length_rootReflection, length_rootReflection]
  constructor
  · rintro ⟨heq | hlt, hne⟩
    · exact (hne heq).elim
    · omega
  · intro hlt
    refine ⟨Or.inr (by omega), ?_⟩
    intro heq
    rw [heq] at hlt
    omega

/-- Strict real-cone comparison agrees with strict canonical Bruhat comparison of reflections. -/
theorem rootOrder_bruhat {n : ℕ} (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) :
    (RootOrder n hthree alpha beta ∧ alpha ≠ beta) ↔
      (BruhatLE n hthree alpha.reflection beta.reflection ∧
        alpha.reflection ≠ beta.reflection) := by
  rw [rootOrder_length, bruhatLE_iff_eq_or_length_lt]
  constructor
  · intro hlt
    exact ⟨Or.inr hlt, fun heq => (ne_of_lt hlt) (congrArg (length n hthree) heq)⟩
  · rintro ⟨heq | hlt, hne⟩
    · exact (hne heq).elim
    · exact hlt

end Schubert.DihedralSplines
