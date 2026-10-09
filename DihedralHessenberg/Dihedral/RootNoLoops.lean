import DihedralHessenberg.Dihedral.RootObjects
import DihedralHessenberg.Dihedral.RootReflections

/-! # Nontrivial positive root reflections -/

namespace Schubert.Dihedral.PositiveRoot

/-- A positive root reflection is not the identity group element. -/
theorem reflection_ne_one {n : ℕ} (alpha : PositiveRoot n) : alpha.reflection ≠ 1 :=
  rootReflection_ne_one alpha.index

end Schubert.Dihedral.PositiveRoot
