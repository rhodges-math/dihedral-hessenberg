import DihedralHessenberg.Dihedral.CyclicIntervals

/-! # Separation of the ordered block evaluation window -/

namespace Schubert.Dihedral.Cyclic

/-- Every later interval in a short ordered window excludes the initial vertex of an earlier one. -/
theorem excludes_earlier {n : ℕ} {hthree : 3 ≤ n} (base : Fin (2 * n)) (size : ℕ)
    (hsize : size ≤ n) (first second : ℕ) (horder : first < second) (hsecond : second ≤ size) :
    vertex n hthree (base + ⟨first, by omega⟩) ∉
      interval n hthree (base + ⟨second, by omega⟩) size := by
  let : NeZero (2 * n) := ⟨by omega⟩
  rw [mem_interval _ _ _ (by omega)]
  have hsub : (base + (⟨first, by omega⟩ : Fin (2 * n))) -
      (base + (⟨second, by omega⟩ : Fin (2 * n))) =
        (⟨first, by omega⟩ : Fin (2 * n)) - (⟨second, by omega⟩ : Fin (2 * n)) := by
    abel
  rw [hsub]
  fin_omega

end Schubert.Dihedral.Cyclic
