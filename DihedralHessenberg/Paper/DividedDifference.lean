import DihedralHessenberg.Paper.DividedDifferenceLabels
import DihedralHessenberg.Paper.Spline
import DihedralHessenberg.Splines.ReflectionDividedDifference
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Polynomial-valued Hessenberg divided differences -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- A selected edge with a left-reflection endpoint has that root's difference divisibility. -/
theorem _root_.Schubert.DihedralSplines.IndexedDD.dvd_sub_of_edge [NeZero n]
    (value : HessenbergSpline ideal) (vertex : DihedralGroup n)
    (index edgeIndex : PositiveRootIndex n) (hselected : edgeIndex ∈ ideal.roots)
    (hendpoint : vertex * rootReflection edgeIndex = rootReflection index * vertex) :
    rootPolynomial n index ∣ (value : DihedralGroup n → CoordinatePolynomial) vertex -
      (value : DihedralGroup n → CoordinatePolynomial) (rootReflection index * vertex) := by
  have hdivides := Ideal.mem_span_singleton.mp
    ((hessenbergGraph ideal).spline_condition value (vertex, ⟨edgeIndex, hselected⟩))
  change polynomialAction n vertex (rootPolynomial n edgeIndex) ∣
    (value : DihedralGroup n → CoordinatePolynomial) vertex -
      (value : DihedralGroup n → CoordinatePolynomial) (vertex * rootReflection edgeIndex)
    at hdivides
  rw [hendpoint] at hdivides
  exact (_root_.Schubert.DihedralSplines.IndexedDD.associated_of_endpoint n vertex edgeIndex index
    hendpoint).symm.dvd.trans hdivides

/-- Reflection pairs are divisible when their nonzero endpoints carry selected edges. -/
theorem _root_.Schubert.DihedralSplines.IndexedDD.dvd_sub_of_support
    (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex)
    (vertex : DihedralGroup n) :
    rootPolynomial n index ∣ (value : DihedralGroup n → CoordinatePolynomial) vertex -
      (value : DihedralGroup n → CoordinatePolynomial) (rootReflection index * vertex) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  by_cases hfirst : (value : DihedralGroup n → CoordinatePolynomial) vertex = 0
  · by_cases hsecond :
      (value : DihedralGroup n → CoordinatePolynomial) (rootReflection index * vertex) = 0
    · rw [hfirst, hsecond, sub_self]
      exact dvd_zero _
    · obtain ⟨edgeIndex, hselected, hendpoint⟩ :=
        hedges (rootReflection index * vertex) hsecond
      have hdivides := _root_.Schubert.DihedralSplines.IndexedDD.dvd_sub_of_edge ideal value
        (rootReflection index * vertex) index edgeIndex hselected hendpoint
      have htwice : rootReflection index * (rootReflection index * vertex) = vertex := by
        rw [← mul_assoc, rootReflection_mul_self, one_mul]
      rw [htwice] at hdivides
      simpa only [neg_sub] using hdivides.neg_right
  · obtain ⟨edgeIndex, hselected, hendpoint⟩ := hedges vertex hfirst
    exact _root_.Schubert.DihedralSplines.IndexedDD.dvd_sub_of_edge ideal value vertex index
      edgeIndex hselected hendpoint

/-- The support-edge hypothesis gives a polynomial-valued divided difference spline. -/
theorem exists_hessenberg_divided_difference
    (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex) :
    ∃ quotient : HessenbergSpline ideal, ∀ vertex,
      rootPolynomial n index * (quotient : DihedralGroup n → CoordinatePolynomial) vertex =
        (value : DihedralGroup n → CoordinatePolynomial) vertex -
          ((dihedralReflectionData n hthree).dot (ideal.roots : Set (PositiveRootIndex n))
            (rootReflection index) value : DihedralGroup n → CoordinatePolynomial) vertex := by
  classical
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  have hexists : ∀ vertex, ∃ polynomial : CoordinatePolynomial,
      rootPolynomial n index * polynomial =
        (value : DihedralGroup n → CoordinatePolynomial) vertex -
          ((dihedralReflectionData n hthree).dot (ideal.roots : Set (PositiveRootIndex n))
            (rootReflection index) value : DihedralGroup n → CoordinatePolynomial) vertex := by
    intro vertex
    have hdivides := (dihedralReflectionData n hthree).label_dvd_dot_numerator
      (ideal.roots : Set (PositiveRootIndex n)) index value vertex
      (_root_.Schubert.DihedralSplines.IndexedDD.dvd_sub_of_support ideal value index hedges vertex)
    obtain ⟨polynomial, hpolynomial⟩ := hdivides
    exact ⟨polynomial, hpolynomial.symm⟩
  choose quotient hquotient using hexists
  have hSpline := (dihedralReflectionData n hthree).reflection_dot_quotient_isSpline
    (ideal.roots : Set (PositiveRootIndex n)) index value quotient
    (rootPolynomial_ne_zero n index) hquotient
    (fun vertex edgeIndex _ => rootPolynomial_edge_dichotomy n vertex edgeIndex index)
  exact ⟨⟨quotient, hSpline⟩, hquotient⟩

/-- Divide a reflection dot numerator when its support has the corresponding selected edges. -/
def hessenbergDividedDifference (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex) :
    HessenbergSpline ideal :=
  Classical.choose (exists_hessenberg_divided_difference ideal value index hedges)

/-- The divided difference satisfies the exact polynomial numerator equation. -/
theorem hessenbergDividedDifference_mul_apply
    (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex)
    (vertex : DihedralGroup n) :
    rootPolynomial n index *
        (hessenbergDividedDifference ideal value index hedges :
          DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) vertex -
        ((dihedralReflectionData n hthree).dot (ideal.roots : Set (PositiveRootIndex n))
          (rootReflection index) value : DihedralGroup n → CoordinatePolynomial) vertex :=
  Classical.choose_spec (exists_hessenberg_divided_difference ideal value index hedges) vertex

/-- The polynomial numerator equation uniquely determines the divided difference spline. -/
theorem hessenbergDividedDifference_unique
    (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex)
    (quotient : HessenbergSpline ideal)
    (hquotient : ∀ vertex,
      rootPolynomial n index * (quotient : DihedralGroup n → CoordinatePolynomial) vertex =
        (value : DihedralGroup n → CoordinatePolynomial) vertex -
          ((dihedralReflectionData n hthree).dot (ideal.roots : Set (PositiveRootIndex n))
            (rootReflection index) value : DihedralGroup n → CoordinatePolynomial) vertex) :
    quotient = hessenbergDividedDifference ideal value index hedges := by
  apply Subtype.ext
  funext vertex
  exact mul_left_cancel₀ (rootPolynomial_ne_zero n index)
    ((hquotient vertex).trans
      (hessenbergDividedDifference_mul_apply ideal value index hedges vertex).symm)

end Schubert.DihedralSplines
