import Schubert.DihedralSplines.FullRightClass

/-! # Full right quotient trace series -/

noncomputable section
namespace Schubert.DihedralSplines.SchubertSpline
open Schubert.Dihedral
private theorem geomCoeff (n degree : ℕ) (scalar : ℂ) :
    PowerSeries.coeff degree
      (∑ index ∈ Finset.range n, (PowerSeries.C scalar * PowerSeries.X) ^ index) =
      if degree < n then scalar ^ degree else 0 := by
  simp only [mul_pow, ← map_pow, map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  simp [Finset.sum_ite_eq, Finset.mem_range]

variable (n : ℕ) [NeZero n] (hthree : 3 ≤ n)

/-- The formal trace series of the full right quotient action. -/
def rightTrace (element : DihedralGroup n) : PowerSeries ℂ :=
  PowerSeries.map ((Pi.evalRingHom (fun _ : DihedralGroup n => ℂ) element).comp
    (TauCeti.repRingCharacter ℂ (DihedralGroup n)))
      (RootSubset.Right.gradedClass (RootSubset.full n) hthree)

omit [NeZero n] in
/-- Its coefficients are traces of the quotient degree operators. -/
theorem rightTrace_coeff (element : DihedralGroup n) (degree : ℕ) :
    PowerSeries.coeff degree (rightTrace n hthree element) =
      (RootSubset.Right.pieceRepresentation (RootSubset.full n) hthree degree).character
        element := by
  rw [rightTrace, PowerSeries.coeff_map, RootSubset.Right.gradedClass_coeff]
  simp only [RingHom.comp_apply, TauCeti.repRingCharacter_of, Pi.evalRingHom_apply]
  exact RootSubset.Right.pieceFDRep_character _ _ _ _

/-- The full right trace at any reflection is its two-term finite series. -/
theorem rightTrace_sr (coordinate : ZMod n) :
    rightTrace n hthree (.sr coordinate) = 1 - PowerSeries.X ^ n := by
  apply PowerSeries.ext
  intro degree
  rw [rightTrace_coeff, right_character_degree, ← coinvariantPieceFDRep_character]
  by_cases hzero : degree = 0
  · subst degree
    rw [Coinvariant.character_zero n hthree]
    simp [show n ≠ 0 from NeZero.ne n]
  · by_cases htop : degree = n
    · subst degree
      rw [Coinvariant.character_top n hthree, signCharacter_sr]
      simp [show n ≠ 0 from NeZero.ne n]
    · by_cases hbelow : degree < n
      · rw [Coinvariant.Middle.character_sr n hthree degree (by omega) hbelow]
        simp [hzero, htop]
      · rw [Coinvariant.character_above n hthree degree (by omega)]
        simp [hzero, htop]

/-- Every rotation trace is the finite paired eigenvalue series. -/
theorem rightTrace_r (coordinate : ZMod n) :
    let root := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
    rightTrace n hthree (.r coordinate) =
      (∑ degree ∈ Finset.range n,
        (PowerSeries.C (root⁻¹ ^ coordinate.val) * PowerSeries.X) ^ degree) +
      (∑ degree ∈ Finset.range n,
        (PowerSeries.C (root ^ coordinate.val) * PowerSeries.X) ^ degree) -
      1 + PowerSeries.X ^ n := by
  apply PowerSeries.ext
  intro degree
  rw [rightTrace_coeff, right_character_degree, ← coinvariantPieceFDRep_character]
  simp only [map_add, map_sub, geomCoeff, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  by_cases hzero : degree = 0
  · subst degree
    rw [Coinvariant.character_zero n hthree]
    norm_num [show 0 < n by omega, show n ≠ 0 from NeZero.ne n]
    omega
  · by_cases htop : degree = n
    · subst degree
      rw [Coinvariant.character_top n hthree, signCharacter_r]
      simp [show n ≠ 0 from NeZero.ne n]
    · by_cases hbelow : degree < n
      · rw [Coinvariant.Middle.character_r n hthree degree (by omega) hbelow]
        simp [hzero, htop, hbelow]
      · rw [Coinvariant.character_above n hthree degree (by omega)]
        simp [hzero, htop, hbelow]

end Schubert.DihedralSplines.SchubertSpline
