import Schubert.DihedralSplines.LeftLowClass
import Schubert.DihedralSplines.QuotientClassSupport
import Schubert.DihedralSplines.LeftEvenMiddleClass
import Schubert.DihedralSplines.QuotientSymmetry

/-! # All-degree virtual classes of even left quotients -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Each even left degree has precisely its fixed and middle coset classes. -/
theorem piece_class_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      (if degree = 0 ∨ degree = 2 * half then 1 else if degree < 2 * half then 2 else 0) +
      if degree = half then
        TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
        TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
        TauCeti.SplitK0.of (Frequency.partialSum n half) -
        TauCeti.SplitK0.of (Frequency.partialSum n (half - 1)) else 0 := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 0 < half := by omega
  by_cases hmiddle : degree = half
  · subst degree
    rw [middle_class_even ideal half hcard hproper, trivial_class_one]
    simp only [hpositive.ne', show half ≠ 2 * half by omega, or_self, ite_false,
      show half < 2 * half by omega, ite_true, ite_true]
    simp
    abel
  by_cases habove : ideal.carrier.ncard < degree
  · rw [piece_class_above ideal degree habove]
    simp [hmiddle, show degree ≠ 0 by omega, show degree ≠ 2 * half by omega,
      show ¬ degree < 2 * half by omega]
  have hbelow : degree ≤ ideal.carrier.ncard := by omega
  by_cases hlow : degree < half
  · rw [low_piece_class ideal half (by omega) hproper degree hlow]
    by_cases hzero : degree = 0
    · subst degree
      simp [hmiddle, hpositive.ne']
    · simp [hzero, hmiddle, show degree ≠ 2 * half by omega,
        show degree < 2 * half by omega]
  have hcomplement : ideal.carrier.ncard - degree < half := by omega
  rw [TauCeti.SplitK0.of_congr (complementary_iso ideal degree hbelow).some,
    low_piece_class ideal half (by omega) hproper _ hcomplement]
  by_cases htop : degree = 2 * half
  · simp [hcard, htop, hpositive.ne', show 2 * half ≠ half by omega]
  · simp [hcard, htop, hmiddle, show degree ≠ 0 by omega,
      show degree < 2 * half by omega, show 2 * half - degree ≠ 0 by omega]

end Schubert.DihedralSplines.HessenbergIdeal.Left
