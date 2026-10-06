import Schubert.Dihedral.RootNormal
import Schubert.Dihedral.AscentSupport
import Schubert.Dihedral.RankTwoRootVectors
import Schubert.Dihedral.RootObjectAction
import Schubert.DihedralSplines.HessenbergVectorDegree
import Schubert.DihedralSplines.HessenbergDegree

/-! # Simple-root support and extremal inversion degrees -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The identity has no selected inversions. -/
theorem length_one (ideal : HessenbergIdeal n hthree) : ideal.toRootSubset.length 1 = 0 := by
  rw [ideal.length_indexed, ideal.indexed.length_one]

/-- Every selected positive root is an inversion of the longest element. -/
theorem length_top (ideal : HessenbergIdeal n hthree) :
    ideal.toRootSubset.length (longestElement n hthree) = ideal.carrier.ncard := by
  rw [ideal.length_indexed, ideal.ncard_indexed]
  exact ideal.indexed.length_alternatingWord_top

/-- An upper-half simple ascent edge persists above its upper endpoint. -/
theorem edge_above (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1)
    (hhalf : n < 2 * length n hthree element + 1)
    (hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges)
    (vertex : DihedralGroup n) (hle : BruhatLE n hthree (alpha.reflection * element) vertex) :
    (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges := by
  have hup : BruhatLE n hthree element (alpha.reflection * element) :=
    bruhatLE_of_length_lt n hthree (by omega)
  have hne : element ≠ alpha.reflection * element := by
    intro heq
    have := congrArg (length n hthree) heq
    omega
  have hrange := ideal.edge_range alpha hsimple element hup hne hedge
  rw [ite_eq_right (by omega)] at hrange
  have hbound := bruhatLE_length_le n hthree hle
  exact hrange vertex (by omega)

end Schubert.DihedralSplines.HessenbergIdeal
