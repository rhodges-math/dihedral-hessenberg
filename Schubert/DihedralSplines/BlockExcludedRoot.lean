import Schubert.DihedralSplines.HessenbergBlock
import Schubert.Dihedral.RootAlternatingLength
import Schubert.Dihedral.LengthParity

/-! # Excluded-root edges leave every admissible block -/

namespace Schubert.DihedralSplines.HessenbergIdeal.Block

open Schubert.Dihedral

private theorem prefix_parity {n : ℕ} {hthree : 3 ≤ n} (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (first second : ℕ) (hfirst : first ≤ n) (hsecond : second ≤ n)
    (gamma : PositiveRoot n)
    (heq : alpha.alternatingProduct beta second =
      alpha.alternatingProduct beta first * gamma.reflection) : first % 2 ≠ second % 2 := by
  have hparity := congrArg (coxeterSystem n hthree).lengthParity heq
  rw [map_mul, CoxeterSystem.lengthParity_eq_ofAdd_length,
    CoxeterSystem.lengthParity_eq_ofAdd_length,
    CoxeterSystem.lengthParity_eq_ofAdd_length] at hparity
  have hadd := congrArg Multiplicative.toAdd hparity
  change (length n hthree (alpha.alternatingProduct beta second) : ZMod 2) =
    (length n hthree (alpha.alternatingProduct beta first) : ZMod 2) +
      (length n hthree gamma.reflection : ZMod 2)
    at hadd
  rw [PositiveRoot.alternating_length alpha beta hpair first hfirst,
    PositiveRoot.alternating_length alpha beta hpair second hsecond] at hadd
  have hodd := (gamma.isReflection hthree).odd_length
  change Odd (length n hthree gamma.reflection) at hodd
  rw [ZMod.natCast_eq_one_iff_odd.mpr hodd] at hadd
  intro hequal
  have hcasts : (first : ZMod 2) = (second : ZMod 2) := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using hequal
  rw [hcasts] at hadd
  simp at hadd

/-- A root absent from the ideal cannot join two vertices of an admissible block. -/
theorem excluded_leaves {n : ℕ} {hthree : 3 ≤ n} {ideal : HessenbergIdeal n hthree}
    (block : Block ideal) (gamma : PositiveRoot n) (hmissing : gamma.val ∉ ideal.carrier)
    (source : DihedralGroup n) (hsource : source ∈ block.vertices) :
    source * gamma.reflection ∉ block.vertices := by
  intro htarget
  obtain ⟨first, hfirst, hsourceEq⟩ :=
    (mem_alternatingBlock block.base source block.alpha block.beta block.half).mp hsource
  obtain ⟨second, hsecond, htargetEq⟩ :=
    (mem_alternatingBlock block.base (source * gamma.reflection)
      block.alpha block.beta block.half).mp htarget
  have heq : block.alpha.alternatingProduct block.beta second =
      block.alpha.alternatingProduct block.beta first * gamma.reflection := by
    apply mul_left_cancel (a := block.base)
    rw [← mul_assoc, hsourceEq, htargetEq]
  have hparity := prefix_parity block.alpha block.beta block.pair first second
    (by have := block.bound; omega) (by have := block.bound; omega) gamma heq
  have hedge := (block.edge first second hfirst hsecond).mpr hparity
  rw [hsourceEq, htargetEq] at hedge
  obtain ⟨delta, hselected, hreflection⟩ := (ideal.toRootSubset.mem_edges _).mp hedge
  have heqRoots : gamma = delta := PositiveRoot.reflection_injective n
    (mul_left_cancel hreflection)
  exact hmissing (heqRoots.symm ▸ hselected)

end Schubert.DihedralSplines.HessenbergIdeal.Block
