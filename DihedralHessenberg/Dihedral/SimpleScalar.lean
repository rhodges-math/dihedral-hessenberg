import DihedralHessenberg.Dihedral.RootScalarCharacter
import DihedralHessenberg.Dihedral.RootAlternatingWords

/-! # Even scalar objects selected by the two simple roots -/

noncomputable section
namespace Schubert.Dihedral

/-- The first simple root selects the even scalar object fixed by its reflection. -/
theorem first_simple_scalar (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (heven : Even n) :
    (simpleRoot n hthree 0).scalarFDRep heven = evenScalarFDRep n heven false := by
  simp [PositiveRoot.scalarFDRep, simpleRoot_zero, PositiveRoot.index_equiv,
    firstSimpleRootIndex, reflectionCoordinate]

/-- The second simple root selects the other even scalar object. -/
theorem second_simple_scalar (n : ℕ) (hthree : 3 ≤ n) (heven : Even n) :
    (simpleRoot n hthree 1).scalarFDRep heven = evenScalarFDRep n heven true := by
  let : Fact (1 < n) := ⟨by omega⟩
  have hone : (1 : ZMod n).val = 1 := by
    rw [ZMod.val_one]
  simp [PositiveRoot.scalarFDRep, simpleRoot_one, PositiveRoot.index_equiv,
    secondSimpleRootIndex, reflectionCoordinate, hone]

end Schubert.Dihedral
