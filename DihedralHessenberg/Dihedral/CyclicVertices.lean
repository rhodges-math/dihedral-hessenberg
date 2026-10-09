import DihedralHessenberg.Dihedral.RootAlternatingProduct
import DihedralHessenberg.Dihedral.RootNormal
import Mathlib.Tactic

/-! # Cyclic enumeration of dihedral vertices -/

noncomputable section

namespace Schubert.Dihedral.Cyclic

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The alternating polygon enumeration of group vertices. -/
def vertex (n : ℕ) (hthree : 3 ≤ n) (index : Fin (2 * n)) : DihedralGroup n :=
  (simpleRoot n hthree 0).alternatingProduct (simpleRoot n hthree 1) index.val

/-- Even positions are rotations with the corresponding cyclic coordinate. -/
theorem even_vertex (half : ℕ) (hbound : 2 * half < 2 * n) :
    vertex n hthree ⟨2 * half, hbound⟩ = DihedralGroup.r (half : ZMod n) := by
  rw [vertex, PositiveRoot.alternating_even, simpleRoot_reflection, simpleRoot_reflection,
    simpleReflection_zero, simpleReflection_one]
  simp only [firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
    sub_zero, DihedralGroup.r_pow, one_mul]

/-- Odd positions are the reflections in the first cyclic orientation. -/
theorem odd_vertex (half : ℕ) (hbound : 2 * half + 1 < 2 * n) :
    vertex n hthree ⟨2 * half + 1, hbound⟩ = DihedralGroup.sr (-(half : ZMod n)) := by
  rw [vertex, PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
    simpleReflection_zero, simpleReflection_one]
  simp only [firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
    sub_zero, DihedralGroup.r_pow, one_mul, DihedralGroup.r_mul_sr, zero_sub]

/-- The parity and half-index determine the group constructor and coordinate. -/
theorem normal (index : Fin (2 * n)) :
    vertex n hthree index = if index.val % 2 = 0 then
      DihedralGroup.r ((index.val / 2 : ℕ) : ZMod n)
      else DihedralGroup.sr (-((index.val / 2 : ℕ) : ZMod n)) := by
  by_cases heven : index.val % 2 = 0
  · rw [ite_eq_left heven]
    have heq : index = ⟨2 * (index.val / 2), by have := index.isLt; omega⟩ :=
      Fin.ext (by change index.val = 2 * (index.val / 2); omega)
    conv_lhs => rw [heq]
    exact even_vertex (index.val / 2) _
  · rw [ite_eq_right heven]
    have heq : index = ⟨2 * (index.val / 2) + 1, by have := index.isLt; omega⟩ :=
      Fin.ext (by change index.val = 2 * (index.val / 2) + 1; omega)
    conv_lhs => rw [heq]
    exact odd_vertex (index.val / 2) _

/-- The cyclic enumeration does not repeat a vertex before one complete circuit. -/
theorem injective : Function.Injective (vertex n hthree) := by
  let : NeZero n := ⟨by omega⟩
  intro first second heq
  have hfirst := first.isLt
  have hsecond := second.isLt
  have hfirstHalf : first.val / 2 < n := by omega
  have hsecondHalf : second.val / 2 < n := by omega
  rw [normal, normal] at heq
  by_cases hfirstEven : first.val % 2 = 0
  · by_cases hsecondEven : second.val % 2 = 0
    · rw [ite_eq_left hfirstEven, ite_eq_left hsecondEven] at heq
      have hcast := DihedralGroup.r.inj heq
      have hval := congrArg ZMod.val hcast
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hfirstHalf,
        Nat.mod_eq_of_lt hsecondHalf] at hval
      exact Fin.ext (by omega)
    · rw [ite_eq_left hfirstEven, ite_eq_right hsecondEven] at heq
      cases heq
  · by_cases hsecondEven : second.val % 2 = 0
    · rw [ite_eq_right hfirstEven, ite_eq_left hsecondEven] at heq
      cases heq
    · rw [ite_eq_right hfirstEven, ite_eq_right hsecondEven] at heq
      have hcast := neg_injective (DihedralGroup.sr.inj heq)
      have hval := congrArg ZMod.val hcast
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hfirstHalf,
        Nat.mod_eq_of_lt hsecondHalf] at hval
      exact Fin.ext (by omega)

/-- Every group vertex occurs in the alternating polygon enumeration. -/
theorem surjective : Function.Surjective (vertex n hthree) := by
  let : NeZero n := ⟨by omega⟩
  intro element
  cases element with
  | r coordinate =>
    refine ⟨⟨2 * coordinate.val, by have := coordinate.val_lt; omega⟩, ?_⟩
    rw [even_vertex, ZMod.natCast_zmod_val]
  | sr coordinate =>
    refine ⟨⟨2 * (-coordinate).val + 1, by have := (-coordinate).val_lt; omega⟩, ?_⟩
    rw [odd_vertex, ZMod.natCast_zmod_val, neg_neg]

/-- A complete cyclic enumeration is a bijection with the dihedral group. -/
def equiv (n : ℕ) (hthree : 3 ≤ n) : Fin (2 * n) ≃ DihedralGroup n :=
  Equiv.ofBijective (vertex n hthree) ⟨injective, surjective⟩

end Schubert.Dihedral.Cyclic
