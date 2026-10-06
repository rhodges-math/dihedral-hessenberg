import Schubert.Dihedral.CosetPairs
import Schubert.Dihedral.TerminalConjugacy

/-! # Adjacent terminal cosets and the simple reflection pair -/

noncomputable section

open CategoryTheory Limits

namespace Schubert.Dihedral.PositiveRoot

/-- The terminal reflection pair has the biproduct of the simple coset objects. -/
theorem terminal_pair_iso (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hbound : 2 * half + 1 < n) :
    Nonempty (((positiveRootEquiv n ⟨2 * half, by omega⟩).cosetFDRep ⊞
      (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).cosetFDRep) ≅
      ((simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep)) :=
  opposite_pairs_iso _ _ _ _ heven (terminal_not_isConj n hthree heven half hbound)
    (simple_not_isConj n hthree heven)

/-- The adjacent terminal coset sum equals the exact simple coset sum in the representation ring. -/
theorem terminal_pair_class (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (heven : Even n)
    (half : ℕ) (hbound : 2 * half + 1 < n) :
    (TauCeti.SplitK0.of (positiveRootEquiv n ⟨2 * half, by omega⟩).cosetFDRep :
      TauCeti.repRing ℂ (DihedralGroup n)) +
      TauCeti.SplitK0.of (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).cosetFDRep =
        TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
          TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep :=
  opposite_pairs_class _ _ _ _ heven (terminal_not_isConj n hthree heven half hbound)
    (simple_not_isConj n hthree heven)

end Schubert.Dihedral.PositiveRoot
