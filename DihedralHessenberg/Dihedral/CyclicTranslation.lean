import DihedralHessenberg.Dihedral.CyclicIntervals

/-! # Rotation translation of cyclic vertex sets -/

namespace Schubert.Dihedral.Cyclic

/-- Multiplication by an even-position vertex adds its cyclic position. -/
theorem even_mul {n : ℕ} {hthree : 3 ≤ n} (first second : Fin (2 * n))
    (heven : Even first.val) :
    vertex n hthree first * vertex n hthree second = vertex n hthree (first + second) := by
  simpa only [ite_eq_left heven, vertex, Fin.add_def] using
    (forward_prefix (n := n) (hthree := hthree) first second.val)

/-- Rotation translation preserves interval size and translates its starting position. -/
theorem interval_translate {n : ℕ} {hthree : 3 ≤ n} (first start : Fin (2 * n))
    (heven : Even first.val) (size : ℕ) :
    (interval n hthree start size).image (fun v => vertex n hthree first * v) =
      interval n hthree (first + start) size := by
  classical
  rw [interval, Finset.image_image, interval]
  apply Finset.image_congr
  intro position _
  dsimp only [Function.comp_apply]
  rw [even_mul _ _ heven]
  congr 1
  apply Fin.ext
  change (first.val + (start.val + position) % (2 * n)) % (2 * n) =
    ((first.val + start.val) % (2 * n) + position) % (2 * n)
  rw [Nat.add_mod_mod, Nat.mod_add_mod, add_assoc]

end Schubert.Dihedral.Cyclic
