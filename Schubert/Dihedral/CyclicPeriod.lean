import Schubert.Dihedral.CyclicVertices
import Schubert.Dihedral.AlternatingAppend

/-! # Periodicity of the polygon enumeration -/

namespace Schubert.Dihedral.PositiveRoot

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Reducing a word length modulo the complete circuit preserves its group vertex. -/
theorem alternating_mod (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) (size : ℕ) :
    alpha.alternatingProduct beta (size % (2 * n)) = alpha.alternatingProduct beta size := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
    by_cases hshort : size < 2 * n
    · rw [Nat.mod_eq_of_lt hshort]
    · have hsum : size = 2 * n + (size - 2 * n) := by omega
      have hprevious : size - 2 * n < size := by omega
      have heven : Even (2 * n) := ⟨n, by omega⟩
      have hmod : size % (2 * n) = (size - 2 * n) % (2 * n) := by
        conv_lhs => rw [hsum]
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      rw [hmod, ih _ hprevious]
      conv_rhs => rw [hsum, alternating_append, alternating_cycle alpha beta hpair,
        ite_eq_left heven, one_mul]

end Schubert.Dihedral.PositiveRoot

namespace Schubert.Dihedral.Cyclic

/-- Arbitrary prefix lengths reduce to the finite cyclic enumeration. -/
theorem vertex_mod {n : ℕ} {hthree : 3 ≤ n} (size : ℕ) :
    vertex n hthree ⟨size % (2 * n), Nat.mod_lt _ (by omega)⟩ =
      (simpleRoot n hthree 0).alternatingProduct (simpleRoot n hthree 1) size :=
  PositiveRoot.alternating_mod _ _ (Or.inl ⟨rfl, rfl⟩) size

end Schubert.Dihedral.Cyclic
