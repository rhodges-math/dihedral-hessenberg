import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Dihedral.ConjugatedLength

/-! # Reflection lengths at simple-root neighbors -/

namespace Schubert.Dihedral.PositiveRoot

/-- The root joining a simple-vector ascent has the two-branch reflection length formula. -/
theorem ascent_length {n : ℕ} (hthree : 3 ≤ n) (alpha gamma : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hup : BruhatLE n hthree element (alpha.reflection * element))
    (hne : element ≠ alpha.reflection * element)
    (hneighbor : alpha.reflection * element = element * gamma.reflection) :
    length n hthree gamma.reflection =
      if 2 * length n hthree element + 1 ≤ n then 2 * length n hthree element + 1
        else 2 * (n - length n hthree element) - 1 := by
  obtain ⟨simple, rfl⟩ : ∃ simple : Fin 2, alpha = simpleRoot n hthree simple := by
    rcases hsimple with hfirst | hsecond
    · exact ⟨0, hfirst⟩
    · exact ⟨1, hsecond⟩
  rw [simpleRoot_reflection] at hup hne hneighbor
  exact _root_.Schubert.Dihedral.IndexedRoots.length_at_simple_ascent n hthree simple element
    gamma.index
    hup hne hneighbor

/-- The root joining a simple-vector descent has the two-branch reflection length formula. -/
theorem descent_length {n : ℕ} (hthree : 3 ≤ n) (alpha gamma : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hdown : BruhatLE n hthree (alpha.reflection * element) element)
    (hne : alpha.reflection * element ≠ element)
    (hneighbor : alpha.reflection * element = element * gamma.reflection) :
    length n hthree gamma.reflection =
      if 2 * length n hthree element - 1 ≤ n then 2 * length n hthree element - 1
        else 2 * (n - length n hthree element) + 1 := by
  obtain ⟨simple, rfl⟩ : ∃ simple : Fin 2, alpha = simpleRoot n hthree simple := by
    rcases hsimple with hfirst | hsecond
    · exact ⟨0, hfirst⟩
    · exact ⟨1, hsecond⟩
  rw [simpleRoot_reflection] at hdown hne hneighbor
  exact _root_.Schubert.Dihedral.IndexedRoots.length_at_simple_descent n hthree simple element
    gamma.index
    hdown hne hneighbor

end Schubert.Dihedral.PositiveRoot
