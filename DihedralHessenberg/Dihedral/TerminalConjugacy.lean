import DihedralHessenberg.Dihedral.Conjugacy
import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Dihedral.ReflectionIndex

/-! # Distinct conjugacy classes of adjacent numbered reflections -/

namespace Schubert.Dihedral

/-- Consecutive root pairs give different reflection conjugacy classes for even parameter. -/
theorem terminal_not_isConj (n : ℕ) (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hbound : 2 * half + 1 < n) :
    ¬IsConj (positiveRootEquiv n ⟨2 * half, by omega⟩).reflection
      (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection := by
  let : NeZero n := ⟨by omega⟩
  rw [PositiveRoot.reflection_equiv, PositiveRoot.reflection_equiv,
    rootReflection_eq_sr_of_even _ (by simp), rootReflection_eq_sr_of_odd _ (by simp)]
  have hfirst : 2 * half / 2 = half := by omega
  have hsecond : (2 * half + 1) / 2 = half := by omega
  simp only [hfirst, hsecond]
  rw [isConj_sr_iff_val_parity_of_even n heven]
  have hdiv : 2 ∣ n := even_iff_two_dvd.mp heven
  rw [ZMod.neg_val', ZMod.val_natCast_of_lt (show half < n by omega)]
  rw [Nat.mod_mod_of_dvd _ hdiv]
  have hcast : (half : ZMod n) + 1 = ((half + 1 : ℕ) : ZMod n) := by push_cast; rfl
  rw [hcast, ZMod.val_natCast_of_lt (show half + 1 < n by omega)]
  have hn : n % 2 = 0 := Nat.even_iff.mp heven
  omega

/-- The simple positive vectors give nonconjugate reflections for even parameter. -/
theorem simple_not_isConj (n : ℕ) (hthree : 3 ≤ n) (heven : Even n) :
    ¬IsConj (simpleRoot n hthree 0).reflection (simpleRoot n hthree 1).reflection := by
  rw [simpleRoot_zero, simpleRoot_one]
  exact terminal_not_isConj n hthree heven 0 (by omega)

end Schubert.Dihedral
