import Schubert.DihedralSplines.HessenbergReflectionLength

/-! # The unique final-layer reflection of an odd-sized Hessenberg ideal -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- An odd-sized ideal contains exactly one root whose reflection length equals its size. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.Reflections.unique_boundary_odd
    (ideal : HessenbergSpace n hthree) (hodd : Odd ideal.roots.card) :
    ∃! index : PositiveRootIndex n, index ∈ ideal.roots ∧
      Schubert.Dihedral.length n hthree (rootReflection index) = ideal.roots.card := by
  have hminimum := ideal.two_le_card
  have hmaximum := ideal.card_le
  have hmod := Nat.odd_iff.mp hodd
  rcases ideal.root_membership_classification with hprefix | ⟨_, hproper, hother⟩
  · let index : PositiveRootIndex n := ⟨ideal.roots.card - 1, by omega⟩
    refine ⟨index, ⟨?_, ?_⟩, ?_⟩
    · apply (hprefix index).mpr
      simp only [index]
      omega
    · rw [length_rootReflection]
      simp only [index]
      omega
    · intro other hmember
      have hvalue := (hprefix other).mp hmember.1
      have hlength := hmember.2
      rw [length_rootReflection] at hlength
      apply Fin.ext
      simp only [index]
      omega
  · let index : PositiveRootIndex n := ⟨ideal.roots.card, hproper⟩
    refine ⟨index, ⟨?_, ?_⟩, ?_⟩
    · exact (hother index).mpr (Or.inr rfl)
    · rw [length_rootReflection]
      simp only [index]
      omega
    · intro other hmember
      have hvalue := (hother other).mp hmember.1
      have hlength := hmember.2
      rw [length_rootReflection] at hlength
      apply Fin.ext
      simp only [index]
      omega

end Schubert.DihedralSplines.HessenbergSpace
