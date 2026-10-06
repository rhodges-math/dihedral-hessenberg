import Schubert.DihedralSplines.LeftOddMiddleClass
import Schubert.DihedralSplines.RightOddMiddleClass

/-! # Middle virtual classes selected by dominance -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- The odd middle class uses the dominant simple vector. -/
theorem middle_class_dominant (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hdominant : ideal.IsDominant alpha) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      2 • TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) +
      TauCeti.SplitK0.of alpha.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n half) := by
  have hdom := hdominant
  obtain ⟨beta, hpair, _⟩ := hdom
  rcases hpair with hfirst | hsecond
  · rcases hfirst with ⟨rfl, _⟩
    obtain ⟨witness⟩ := ideal.middle_odd half hcard hproper _ hdominant
    exact middle_class_odd ideal half hcard hproper 0 witness
  · rcases hsecond with ⟨rfl, _⟩
    obtain ⟨witness⟩ := ideal.middle_odd half hcard hproper _ hdominant
    exact middle_class_odd ideal half hcard hproper 1 witness
end Left

namespace Right
/-- The odd middle class uses the dominant simple vector. -/
theorem middle_class_dominant (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hdominant : ideal.IsDominant alpha) :
    (TauCeti.SplitK0.of (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (frequencyFDRep n half) +
      TauCeti.SplitK0.of alpha.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n half) := by
  have hdom := hdominant
  obtain ⟨beta, hpair, _⟩ := hdom
  rcases hpair with hfirst | hsecond
  · rcases hfirst with ⟨rfl, _⟩
    obtain ⟨witness⟩ := ideal.middle_odd half hcard hproper _ hdominant
    exact middle_class_odd ideal half hcard hproper 0 witness
  · rcases hsecond with ⟨rfl, _⟩
    obtain ⟨witness⟩ := ideal.middle_odd half hcard hproper _ hdominant
    exact middle_class_odd ideal half hcard hproper 1 witness
end Right

end Schubert.DihedralSplines.HessenbergIdeal
