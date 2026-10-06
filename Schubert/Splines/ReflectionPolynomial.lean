import Schubert.Splines.ReflectionDivisibility
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Basic.Complex.Basic

/-! # Polynomial differences of linear reflections

The column extension of a linear reflection fixes polynomials modulo the linear
form corresponding to its reflected normal vector.
-/

namespace Schubert.Splines

/-- The polynomial extension of a linear reflection fixes polynomials modulo its normal form. -/
theorem reflection_sub_dvd {d : ℕ} (normal : Fin d → ℂ)
    (functional : Module.Dual ℂ (Fin d → ℂ)) (hreflection : functional normal = 2)
    (polynomial : MvPolynomial (Fin d) ℂ) :
    (∑ index, MvPolynomial.C (normal index) * MvPolynomial.X index) ∣
      polynomial - MvPolynomial.aeval (fun coordinate =>
        ∑ index, MvPolynomial.C ((Module.reflection hreflection)
          (Pi.single coordinate (1 : ℂ)) index) * MvPolynomial.X index) polynomial := by
  classical
  have hcolumn (coordinate : Fin d) :
      (∑ index, MvPolynomial.C ((Module.reflection hreflection)
        (Pi.single coordinate (1 : ℂ)) index) * MvPolynomial.X index) =
      MvPolynomial.X coordinate -
        MvPolynomial.C (functional (Pi.single coordinate (1 : ℂ))) *
          ∑ index, MvPolynomial.C (normal index) * MvPolynomial.X index := by
    simp only [Module.reflection_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_sub, map_mul, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    congr 1
    simp [Pi.single_apply]
  simp_rw [hcolumn]
  exact polynomial_rank_one_substitution_sub_dvd _ _ polynomial

end Schubert.Splines

namespace Schubert.Splines

/-- The standard symmetric bilinear pairing with a coordinate normal. -/
def normalPairing {d : ℕ} (normal : Fin d → ℂ) : Module.Dual ℂ (Fin d → ℂ) :=
  ∑ coordinate, normal coordinate • LinearMap.proj coordinate

/-- The normal pairing is the sum of coordinate products. -/
theorem normalPairing_apply {d : ℕ} (normal vector : Fin d → ℂ) :
    normalPairing normal vector = ∑ coordinate, normal coordinate * vector coordinate := by
  simp [normalPairing, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The symmetric bilinear reflection in a coordinate normal. -/
noncomputable def normalReflection {d : ℕ} (normal : Fin d → ℂ) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  Module.preReflection normal ((2 / normalPairing normal normal) • normalPairing normal)

/-- A nonisotropic normal has normalized pairing equal to two. -/
theorem normalizedPairing_normal {d : ℕ} (normal : Fin d → ℂ)
    (hnormal : normalPairing normal normal ≠ 0) :
    (((2 / normalPairing normal normal) • normalPairing normal) :
      Module.Dual ℂ (Fin d → ℂ)) normal = 2 := by
  simp only [LinearMap.smul_apply, smul_eq_mul]
  exact div_mul_cancel₀ 2 hnormal

/-- The symmetric normal reflection is the corresponding linear reflection. -/
theorem normalReflection_eq {d : ℕ} (normal : Fin d → ℂ)
    (hnormal : normalPairing normal normal ≠ 0) :
    normalReflection normal =
      (Module.reflection (normalizedPairing_normal normal hnormal)).toLinearMap := rfl

/-- The normal reflection has the standard symmetric bilinear formula. -/
theorem normalReflection_apply {d : ℕ} (normal vector : Fin d → ℂ) :
    normalReflection normal vector = vector -
      (2 * (∑ coordinate, vector coordinate * normal coordinate) /
        (∑ coordinate, normal coordinate * normal coordinate)) • normal := by
  rw [normalReflection, Module.preReflection_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, normalPairing_apply]
  rw [div_mul_eq_mul_div]
  congr 2
  simp only [mul_comm]

/-- The column extension of a symmetric reflection fixes polynomials modulo its normal form. -/
theorem normalReflection_sub_dvd {d : ℕ} (normal : Fin d → ℂ)
    (hnormal : normalPairing normal normal ≠ 0) (polynomial : MvPolynomial (Fin d) ℂ) :
    (∑ coordinate, MvPolynomial.C (normal coordinate) * MvPolynomial.X coordinate) ∣
      polynomial - MvPolynomial.aeval (fun coordinate =>
        ∑ index, MvPolynomial.C (normalReflection normal
          (Pi.single coordinate (1 : ℂ)) index) * MvPolynomial.X index) polynomial :=
  reflection_sub_dvd normal ((2 / normalPairing normal normal) • normalPairing normal)
    (normalizedPairing_normal normal hnormal) polynomial

end Schubert.Splines

namespace Schubert.Splines

/-- The column polynomial extension of the symmetric normal reflection. -/
noncomputable def normalExtension {d : ℕ} (normal : Fin d → ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  MvPolynomial.aeval (fun coordinate => ∑ index,
    MvPolynomial.C (normalReflection normal (Pi.single coordinate (1 : ℂ)) index) *
      MvPolynomial.X index)

/-- A variable is sent to the linear form of its reflected coordinate basis vector. -/
theorem normalExtension_X {d : ℕ} (normal : Fin d → ℂ) (coordinate : Fin d) :
    normalExtension normal (MvPolynomial.X coordinate) = ∑ index,
      MvPolynomial.C (normalReflection normal (Pi.single coordinate (1 : ℂ)) index) *
        MvPolynomial.X index := MvPolynomial.aeval_X _ _

end Schubert.Splines
