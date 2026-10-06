import Schubert.Dihedral.ScalarCosetBound
import Schubert.DihedralSplines.ScalarKernel
import Schubert.DihedralSplines.QuotientSurvival

/-! # Even scalar constituents surviving at middle degree -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Both extra even characters survive in the middle quotient. -/
theorem middle_scalar_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (heven : Even n) (negative : Bool) :
    1 ≤ Module.finrank ℂ (evenScalarFDRep n heven negative ⟶
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  let : Simple (evenScalarFDRep n heven negative) := evenScalarFDRep_simple n heven negative
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hbound := middle_coset_survival ideal half hcard hproper first second
    (evenScalarFDRep n heven negative)
  have hcoset := even_scalar_coset_bound hthree heven negative
  rw [removed_scalar_zero ideal half (by omega) hproper (by omega)
    (evenScalarFDRep n heven negative) (evenScalarFDRep_finrank n heven negative)
    (even_scalar_not_trivial heven negative), zero_add] at hbound
  exact hcoset.trans hbound
end Left

namespace Right
/-- Both extra even characters survive in the middle quotient. -/
theorem middle_scalar_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (heven : Even n) (negative : Bool) :
    1 ≤ Module.finrank ℂ (evenScalarFDRep n heven negative ⟶
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
  let : Simple (evenScalarFDRep n heven negative) := evenScalarFDRep_simple n heven negative
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hbound := middle_coset_survival ideal half hcard hproper first second
    (evenScalarFDRep n heven negative)
  have hcoset := even_scalar_coset_bound hthree heven negative
  rw [removed_scalar_zero ideal half (by omega) hproper (by omega)
    (evenScalarFDRep n heven negative) (evenScalarFDRep_finrank n heven negative)
    (even_scalar_not_trivial heven negative), zero_add] at hbound
  exact hcoset.trans hbound
end Right

end Schubert.DihedralSplines.HessenbergIdeal
