import Schubert.Dihedral.RootSubsetCard
import Schubert.DihedralSplines.HessenbergObjects
import Schubert.DihedralSplines.HessenbergInversions

/-! # Cardinalities and inversions of vector Hessenberg ideals -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The indexed finite carrier is the index set of the vector carrier. -/
theorem indexed_roots (ideal : HessenbergIdeal n hthree) :
    (ideal.indexed.roots : Set (PositiveRootIndex n)) = ideal.toRootSubset.indices := by
  ext index
  exact ideal.toRootSubset.mem_indicesFinset index

/-- The vector carrier is precisely the image of the indexed ideal. -/
theorem image_indexed (ideal : HessenbergIdeal n hthree) :
    positiveRoot n '' (ideal.indexed.roots : Set (PositiveRootIndex n)) = ideal.carrier := by
  rw [ideal.indexed_roots]
  exact ideal.toRootSubset.image_indices

/-- The vector ideal has the same finite cardinality as its indexed ideal. -/
theorem ncard_indexed (ideal : HessenbergIdeal n hthree) :
    ideal.carrier.ncard = ideal.indexed.roots.card := ideal.toRootSubset.ncard_indices

/-- The H-length counts the same roots before and after vector transport. -/
theorem length_indexed (ideal : HessenbergIdeal n hthree) (element : DihedralGroup n) :
    ideal.toRootSubset.length element = ideal.indexed.length element :=
  ideal.toRootSubset.length_indices hthree element

/-- The H-inversion set is the vector image of the indexed H-inversions. -/
theorem image_inversions (ideal : HessenbergIdeal n hthree) (element : DihedralGroup n) :
    positiveRoot n '' (ideal.indexed.inversions element : Set (PositiveRootIndex n)) =
      ideal.toRootSubset.inversions element :=
  ideal.toRootSubset.inversion_indices hthree element

end Schubert.DihedralSplines.HessenbergIdeal
