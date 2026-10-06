import Schubert.Dihedral.RootCosetObjects

/-! # Rotation coordinates and fixed points for root-reflection cosets -/

noncomputable section

namespace Schubert.Dihedral.PositiveRoot

/-- The standard root-reflection coset represented by a rotation. -/
def rotationCoset {n : ℕ} (alpha : PositiveRoot n) (coordinate : ZMod n) : alpha.Cosets :=
  QuotientGroup.mk (DihedralGroup.r coordinate)

/-- Rotation coordinates identify the cyclic coordinates with the standard cosets. -/
def rotationEquiv {n : ℕ} [NeZero n] (alpha : PositiveRoot n) : ZMod n ≃ alpha.Cosets :=
  rotationCosetEquiv alpha.index

/-- A rotation acts by adding its coordinate to the coset coordinate. -/
theorem rotation_action {n : ℕ} (alpha : PositiveRoot n) (first second : ZMod n) :
    DihedralGroup.r first • alpha.rotationCoset second = alpha.rotationCoset (first + second) :=
  r_smul_rotationCoset alpha.index first second

/-- A reflection acts by the affine involution determined by the generating reflection. -/
theorem reflection_action {n : ℕ} (alpha : PositiveRoot n) (generating first second : ZMod n)
    (hcoordinate : alpha.reflection = DihedralGroup.sr generating) :
    DihedralGroup.sr first • alpha.rotationCoset second =
      alpha.rotationCoset (generating - first - second) := by
  have hgenerating : reflectionCoordinate alpha.index = generating :=
    DihedralGroup.sr.inj ((rootReflection_eq_sr alpha.index).symm.trans hcoordinate)
  exact hgenerating ▸ sr_smul_rotationCoset alpha.index first second

/-- The identity fixes all n root-reflection cosets. -/
theorem fixed_cosets_one {n : ℕ} [NeZero n] (alpha : PositiveRoot n) :
    Nat.card (MulAction.fixedBy alpha.Cosets (1 : DihedralGroup n)) = n :=
  card_fixedBy_one_reflectionCosets alpha.index

/-- Every nonidentity rotation fixes no root-reflection coset. -/
theorem fixed_cosets_rotation {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (coordinate : ZMod n) (hne : coordinate ≠ 0) :
    Nat.card (MulAction.fixedBy alpha.Cosets (DihedralGroup.r coordinate)) = 0 :=
  card_fixedBy_r_reflectionCosets alpha.index coordinate hne

/-- For odd n every reflection fixes one root-reflection coset. -/
theorem fixed_cosets_odd {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (hodd : Odd n) (coordinate : ZMod n) :
    Nat.card (MulAction.fixedBy alpha.Cosets (DihedralGroup.sr coordinate)) = 1 :=
  card_fixedBy_sr_reflectionCosets_of_odd alpha.index hodd coordinate

/-- For even n a reflection fixes two or zero cosets according to its conjugacy class. -/
theorem fixed_cosets_even {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (heven : Even n) (coordinate : ZMod n) :
    Nat.card (MulAction.fixedBy alpha.Cosets (DihedralGroup.sr coordinate)) =
      if IsConj (DihedralGroup.sr coordinate) alpha.reflection then 2 else 0 :=
  card_fixedBy_sr_reflectionCosets_of_even alpha.index heven coordinate

end Schubert.Dihedral.PositiveRoot
