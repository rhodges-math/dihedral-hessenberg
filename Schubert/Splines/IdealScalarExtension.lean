import Mathlib.RingTheory.Ideal.Maps

/-! # Extension ideals and scalar multiples of an algebra

An ideal extended through an algebra map is precisely its product with the whole
algebra as a module, after restricting scalar multiplication to the base ring.
-/

namespace Schubert.Splines

universe u v

/-- Extending an ideal to an algebra agrees with its scalar product with the whole algebra. -/
theorem mapIdeal_restrictScalars_eq_smul_top {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (ideal : Ideal R) :
    (Ideal.map (algebraMap R A) ideal).restrictScalars R =
      ideal • (⊤ : Submodule R A) := by
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top, Submodule.restrictScalars_top] using
    Submodule.restrictScalars_map_smul_eq ideal (⊤ : Submodule A A)

end Schubert.Splines
