import Mathlib.RingTheory.Ideal.Span
import Schubert.Splines.PolynomialCongruence

/-! # Divisibility of polynomial reflection differences

If a polynomial substitution fixes each variable modulo a principal ideal, then it fixes
every polynomial modulo that ideal. This proves divisibility for rank-one substitutions,
including reflections in an arbitrary finite coordinate space with its standard bilinear form.
-/

namespace Schubert.Splines

universe u v

variable {K : Type u} {T : Type v} [CommRing K]

/-- Congruence on variables implies divisibility of every substitution difference. -/
theorem polynomial_substitution_sub_dvd (label : MvPolynomial T K)
    (substitution : T → MvPolynomial T K)
    (hvariables : ∀ index, label ∣ MvPolynomial.X index - substitution index)
    (polynomial : MvPolynomial T K) :
    label ∣ polynomial - MvPolynomial.aeval substitution polynomial := by
  apply Ideal.mem_span_singleton.mp
  apply polynomial_hom_sub_mem (Ideal.span {label}) (AlgHom.id K (MvPolynomial T K))
    (MvPolynomial.aeval substitution)
  intro index
  simpa only [AlgHom.id_apply, MvPolynomial.aeval_X, Ideal.mem_span_singleton] using
    hvariables index

/-- A substitution changing each variable by a multiple of one label fixes polynomials modulo it. -/
theorem polynomial_rank_one_substitution_sub_dvd (label : MvPolynomial T K)
    (coefficient : T → K) (polynomial : MvPolynomial T K) :
    label ∣ polynomial -
      MvPolynomial.aeval (fun index => MvPolynomial.X index -
        MvPolynomial.C (coefficient index) * label) polynomial := by
  apply polynomial_substitution_sub_dvd
  intro index
  refine ⟨MvPolynomial.C (coefficient index), ?_⟩
  rw [sub_sub_cancel, mul_comm]

section Field

variable {F : Type u} [Field F] [Fintype T]

/-- The standard bilinear reflection in a coordinate normal fixes polynomials modulo its form. -/
theorem bilinear_reflection_polynomial_sub_dvd (normal : T → F)
    (polynomial : MvPolynomial T F) :
    let normalForm : MvPolynomial T F :=
      ∑ index, MvPolynomial.C (normal index) * MvPolynomial.X index
    normalForm ∣ polynomial -
      MvPolynomial.aeval (fun index => MvPolynomial.X index -
        MvPolynomial.C (2 * normal index / (∑ coordinate, normal coordinate * normal coordinate)) *
          normalForm) polynomial :=
  polynomial_rank_one_substitution_sub_dvd _ _ polynomial

/-- The linear polynomial of a reflected coordinate vector gives a rank-one substitution. -/
theorem reflection_column_polynomial [DecidableEq T] (normal : T → F) (coordinate : T) :
    (∑ index, MvPolynomial.C ((Pi.single coordinate (1 : F) : T → F) index -
        (2 * normal coordinate / (∑ position, normal position * normal position)) * normal index) *
      MvPolynomial.X index) =
    MvPolynomial.X coordinate -
      MvPolynomial.C (2 * normal coordinate / (∑ position, normal position * normal position)) *
        ∑ index, MvPolynomial.C (normal index) * MvPolynomial.X index := by
  have hbasis : (∑ index, MvPolynomial.C ((Pi.single coordinate (1 : F) : T → F) index) *
      MvPolynomial.X index) = MvPolynomial.X coordinate := by
    simp [Pi.single_apply]
  simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
  rw [hbasis]
  congr 1
  simp only [mul_assoc, Finset.mul_sum]

/-- The polynomial extension of a bilinear reflection has difference divisible by its normal form.
-/
theorem reflection_extension_polynomial_sub_dvd [DecidableEq T] (normal : T → F)
    (polynomial : MvPolynomial T F) :
    (∑ index, MvPolynomial.C (normal index) * MvPolynomial.X index) ∣ polynomial -
      MvPolynomial.aeval (fun coordinate => ∑ index,
        MvPolynomial.C ((Pi.single coordinate (1 : F) : T → F) index -
          (2 * normal coordinate /
            (∑ position, normal position * normal position)) * normal index) *
            MvPolynomial.X index) polynomial := by
  simpa only [reflection_column_polynomial] using
    bilinear_reflection_polynomial_sub_dvd normal polynomial

end Field

end Schubert.Splines
