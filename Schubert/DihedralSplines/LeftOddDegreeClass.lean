import Schubert.DihedralSplines.LeftLowClass
import Schubert.DihedralSplines.QuotientClassSupport
import Schubert.DihedralSplines.MiddleDominantClass
import Schubert.DihedralSplines.QuotientSymmetry

/-! # All-degree virtual classes of odd left quotients -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Each odd left degree has precisely its fixed and middle coset classes. -/
theorem piece_class_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hdominant : ideal.IsDominant alpha) (degree : ℕ) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      (if degree = 0 ∨ degree = 2 * half + 1 then 1 else if degree < 2 * half + 1 then 2 else 0) +
      if degree = half ∨ degree = half + 1 then
        TauCeti.SplitK0.of alpha.cosetFDRep -
        TauCeti.SplitK0.of (Frequency.partialSum n half) else 0 := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 0 < half := by omega
  by_cases hmiddle : degree = half ∨ degree = half + 1
  · have hclass : (TauCeti.SplitK0.of
          (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
          TauCeti.repRing ℂ (DihedralGroup n)) =
        TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
      rcases hmiddle with hfirst | hsecond
      · rw [hfirst]
      · rw [TauCeti.SplitK0.of_congr (complementary_iso ideal degree (by omega)).some]
        congr 2
        omega
    rw [hclass, middle_class_dominant ideal half hcard hproper alpha hdominant,
      trivial_class_one]
    simp only [show degree ≠ 0 by omega, show degree ≠ 2 * half + 1 by omega,
      or_self, ite_false, show degree < 2 * half + 1 by omega, ite_true, hmiddle]
    simp
    abel
  by_cases habove : ideal.carrier.ncard < degree
  · rw [piece_class_above ideal degree habove]
    simp [hmiddle, show degree ≠ 0 by omega, show degree ≠ 2 * half + 1 by omega,
      show ¬ degree < 2 * half + 1 by omega]
  have hbelow : degree ≤ ideal.carrier.ncard := by omega
  by_cases hlow : degree < half
  · rw [low_piece_class ideal half (by omega) hproper degree hlow]
    by_cases hzero : degree = 0
    · subst degree
      simp [show 0 ≠ half by omega]
    · simp [hzero, hmiddle, show degree ≠ 2 * half + 1 by omega,
        show degree < 2 * half + 1 by omega]
  have hcomplement : ideal.carrier.ncard - degree < half := by omega
  rw [TauCeti.SplitK0.of_congr (complementary_iso ideal degree hbelow).some,
    low_piece_class ideal half (by omega) hproper _ hcomplement]
  rw [ite_eq_right hmiddle]
  by_cases htop : degree = 2 * half + 1
  · simp [hcard, htop]
  · simp [hcard, htop, show degree ≠ 0 by omega,
      show degree < 2 * half + 1 by omega, show 2 * half + 1 - degree ≠ 0 by omega]

end Schubert.DihedralSplines.HessenbergIdeal.Left
