import Schubert.FiniteGroupCharacters.PermutationEquiv
import Schubert.Dihedral.BlockCosetOrbit
import Schubert.Dihedral.CosetFDRep
import TauCeti.RepresentationTheory.RepresentationRing.Basic

/-! # Permutation representations of alternating-block orbits -/

noncomputable section

open CategoryTheory
open scoped Pointwise

namespace Schubert.Dihedral

/-- The first block orbit carries the permutation object of its terminal-root cosets. -/
theorem first_block_permutation {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    Nonempty ((positiveRootEquiv n ⟨2 * half, by omega⟩).cosetFDRep ≅
      FDRep.of (Representation.ofMulAction ℂ (DihedralGroup n)
        (MulAction.orbit (DihedralGroup n)
          (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half)))) := by
  obtain ⟨equivalence, hequivariant⟩ := first_block_cosets (hthree := hthree) half hbound
  exact Schubert.FiniteGroupCharacters.permutation_iso equivalence hequivariant

/-- The second block orbit carries the permutation object of its terminal-root cosets. -/
theorem second_block_permutation {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    Nonempty ((positiveRootEquiv n ⟨2 * half + 1, hbound⟩).cosetFDRep ≅
      FDRep.of (Representation.ofMulAction ℂ (DihedralGroup n)
        (MulAction.orbit (DihedralGroup n)
          (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half)))) := by
  obtain ⟨equivalence, hequivariant⟩ := second_block_cosets (hthree := hthree) half hbound
  exact Schubert.FiniteGroupCharacters.permutation_iso equivalence hequivariant

/-- The first block-orbit class is the terminal-root coset class. -/
theorem first_block_class {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    (TauCeti.SplitK0.of ((positiveRootEquiv n ⟨2 * half, by omega⟩).cosetFDRep) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
        TauCeti.SplitK0.of (FDRep.of (Representation.ofMulAction ℂ (DihedralGroup n)
          (MulAction.orbit (DihedralGroup n)
            (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half)))) := by
  obtain ⟨isomorphism⟩ := first_block_permutation (hthree := hthree) half hbound
  exact TauCeti.SplitK0.of_congr isomorphism

/-- The second block-orbit class is the terminal-root coset class. -/
theorem second_block_class {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    (TauCeti.SplitK0.of ((positiveRootEquiv n ⟨2 * half + 1, hbound⟩).cosetFDRep) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
        TauCeti.SplitK0.of (FDRep.of (Representation.ofMulAction ℂ (DihedralGroup n)
          (MulAction.orbit (DihedralGroup n)
            (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half)))) := by
  obtain ⟨isomorphism⟩ := second_block_permutation (hthree := hthree) half hbound
  exact TauCeti.SplitK0.of_congr isomorphism

end Schubert.Dihedral
