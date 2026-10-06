import Schubert.Dihedral.RootAlternatingLength
import Schubert.Dihedral.RootReflectionVectors
import Schubert.Dihedral.NormalForms
import Schubert.Dihedral.RootNormal

/-! # Concatenation and folded lengths of alternating products -/

namespace Schubert.Dihedral.PositiveRoot

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Concatenation switches the two generators after an odd prefix. -/
theorem alternating_append (alpha beta : PositiveRoot n) (size tail : ℕ) :
    alpha.alternatingProduct beta (size + tail) =
      alpha.alternatingProduct beta size *
        (if Even size then alpha.alternatingProduct beta tail
          else beta.alternatingProduct alpha tail) := by
  induction size generalizing alpha beta with
  | zero => simp only [zero_add, alternating_zero, ite_eq_left (by decide : Even 0), one_mul]
  | succ size ih =>
    rw [Nat.succ_add, alternating_succ, ih, alternating_succ, mul_assoc]
    by_cases heven : Even size
    · have hodd : ¬ Even (size + 1) := by simpa [Nat.even_add_one] using heven
      rw [ite_eq_left heven, ite_eq_right hodd]
    · have hnext : Even (size + 1) := by simpa [Nat.even_add_one] using heven
      rw [ite_eq_right heven, ite_eq_left hnext]

/-- A complete alternating circuit is the identity. -/
theorem alternating_cycle (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) :
    alpha.alternatingProduct beta (2 * n) = 1 := by
  rw [alternating_even]
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [simpleRoot_reflection, simpleReflection_zero, simpleReflection_one,
      firstSimpleReflection, secondSimpleReflection, DihedralGroup.r_pow]

/-- An alternating product traverses the two reduced chains of the polygon. -/
theorem alternating_folded_length (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (size : ℕ) (hbound : size ≤ 2 * n) :
    length n hthree (alpha.alternatingProduct beta size) = min size (2 * n - size) := by
  by_cases hshort : size ≤ n
  · rw [alternating_length alpha beta hpair size hshort, min_eq_left (by omega)]
  · have htail : 2 * n - size ≤ n := by omega
    have hsum : size + (2 * n - size) = 2 * n := by omega
    have hprod := alternating_append alpha beta size (2 * n - size)
    rw [hsum, alternating_cycle alpha beta hpair] at hprod
    rw [min_eq_right (by omega : 2 * n - size ≤ size)]
    have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
        (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
      rcases hpair with hfirst | hsecond
      · exact Or.inr ⟨hfirst.2, hfirst.1⟩
      · exact Or.inl ⟨hsecond.2, hsecond.1⟩
    split_ifs at hprod with heven
    · have heq : alpha.alternatingProduct beta size =
          (alpha.alternatingProduct beta (2 * n - size))⁻¹ := by
        exact eq_inv_of_mul_eq_one_left hprod.symm
      rw [heq, length_inv, alternating_length alpha beta hpair _ htail]
    · have heq : alpha.alternatingProduct beta size =
          (beta.alternatingProduct alpha (2 * n - size))⁻¹ := by
        exact eq_inv_of_mul_eq_one_left hprod.symm
      rw [heq, length_inv, alternating_length beta alpha hreverse _ htail]


/-- Inversion reverses the generator order precisely for even alternating products. -/
theorem alternating_inv (alpha beta : PositiveRoot n) (size : ℕ) :
    (alpha.alternatingProduct beta size)⁻¹ =
      if Even size then beta.alternatingProduct alpha size
        else alpha.alternatingProduct beta size := by
  by_cases heven : Even size
  · rw [ite_eq_left heven]
    obtain ⟨half, hhalf⟩ := heven
    have hsize : size = 2 * half := by omega
    rw [hsize, alternating_even, alternating_even]
    simp only [← inv_pow, mul_inv_rev, reflection_inv]
  · have hodd := Nat.not_even_iff_odd.mp heven
    obtain ⟨half, hhalf⟩ := hodd
    have hsize : size = 2 * half + 1 := by omega
    rw [ite_eq_right heven, hsize, alternating_odd]
    simp only [mul_inv_rev, ← inv_pow, reflection_inv]
    exact (mul_pow_mul alpha.reflection beta.reflection half).symm

end Schubert.Dihedral.PositiveRoot
