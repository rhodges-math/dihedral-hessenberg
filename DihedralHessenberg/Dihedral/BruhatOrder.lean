import DihedralHessenberg.Dihedral.RootReflections

/-! # Canonical Bruhat order as local order data

The canonical relation supplies a partial order and a well-founded strict order.
These are named structures, so applications can install them locally.
-/

namespace Schubert.Dihedral

/-- The canonical Bruhat partial order on the dihedral group. -/
noncomputable abbrev bruhatPartialOrder (n : ℕ) (hthree : 3 ≤ n) :
    PartialOrder (DihedralGroup n) :=
  (coxeterSystem n hthree).bruhatPartialOrder

/-- The order relation of the named partial order is canonical Bruhat comparison. -/
theorem bruhatPartialOrder_le (n : ℕ) (hthree : 3 ≤ n) :
    (bruhatPartialOrder n hthree).le = BruhatLE n hthree := rfl

/-- Strict Bruhat comparison is weak comparison between distinct elements. -/
theorem bruhatPartialOrder_lt (n : ℕ) (hthree : 3 ≤ n) (u w : DihedralGroup n) :
    (bruhatPartialOrder n hthree).lt u w ↔ BruhatLE n hthree u w ∧ u ≠ w :=
  (coxeterSystem n hthree).bruhatPartialOrder_lt

/-- Canonical length makes the strict Bruhat order well founded. -/
theorem bruhatPartialOrder_wellFoundedLT (n : ℕ) (hthree : 3 ≤ n) :
    @WellFoundedLT (DihedralGroup n) (bruhatPartialOrder n hthree).toLT := by
  constructor
  have hsub : Subrelation (bruhatPartialOrder n hthree).lt
      (measure (length n hthree)).rel := by
    intro u w hlt
    obtain ⟨hle, hne⟩ := (bruhatPartialOrder_lt n hthree u w).mp hlt
    exact CoxeterSystem.BruhatLE.length_lt_of_ne hle hne
  exact (Subrelation.wf hsub (measure (length n hthree)).wf).apply

end Schubert.Dihedral
