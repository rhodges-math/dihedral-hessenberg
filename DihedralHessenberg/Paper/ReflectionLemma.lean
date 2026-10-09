import DihedralHessenberg.Splines.ReflectionPolynomial

/-! # Reflection differences in arbitrary complex dimension -/

namespace Schubert.DihedralSplines

open Schubert.Splines

/-- A polynomial and its symmetric reflected image differ by a multiple of the normal form. -/
theorem reflection_difference {d : ℕ} (alpha : Fin d → ℂ)
    (hnormal : (∑ coordinate, alpha coordinate * alpha coordinate) ≠ 0)
    (polynomial : MvPolynomial (Fin d) ℂ) :
    (∑ coordinate, MvPolynomial.C (alpha coordinate) * MvPolynomial.X coordinate) ∣
      polynomial - normalExtension alpha polynomial := by
  apply normalReflection_sub_dvd
  simpa only [normalPairing_apply] using hnormal

end Schubert.DihedralSplines
