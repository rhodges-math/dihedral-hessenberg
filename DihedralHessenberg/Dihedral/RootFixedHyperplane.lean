import DihedralHessenberg.Dihedral.FaithfulRealization
import DihedralHessenberg.Dihedral.RootAxioms

/-! # The orthogonal fixed hyperplane of a root reflection -/

namespace Schubert.Dihedral.PositiveRoot

/-- Reflection fixes exactly the vectors orthogonal to its unit normal. -/
theorem reflection_fixed {n : ℕ} (alpha : PositiveRoot n) (vector : RealPlane) :
    realAction n alpha.reflection vector = vector ↔ realBilinearForm vector alpha.val = 0 := by
  rw [alpha.realAction_reflection]
  have hnormal : alpha.val ≠ 0 := by
    intro hzero
    have hunit := roots_unit alpha.val (Or.inl alpha.property)
    rw [hzero] at hunit
    norm_num [realBilinearForm] at hunit
  constructor
  · intro hfixed
    have hzero : (2 * realBilinearForm vector alpha.val) • alpha.val = 0 :=
      sub_eq_self.mp hfixed
    have hscalar := (smul_eq_zero.mp hzero).resolve_right hnormal
    linarith
  · intro horthogonal
    rw [horthogonal]
    simp

end Schubert.Dihedral.PositiveRoot
