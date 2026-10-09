import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Paper.RootLayerOrder

/-! # The simple-root cone order on positive vectors -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Comparison of positive vectors by the nonnegative real simple-root cone. -/
def RootOrder (n : ℕ) (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) : Prop :=
  ∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
    beta.val - alpha.val = first • (simpleRoot n hthree 0).val +
      second • (simpleRoot n hthree 1).val

/-- Alternating indexing preserves the real cone order. -/
theorem rootOrder_indices {n : ℕ} {hthree : 3 ≤ n} (alpha beta : PositiveRoot n) :
    RootOrder n hthree alpha beta ↔ RootLE n hthree alpha.index beta.index := by
  simp only [RootOrder, RootLE, PositiveRoot.index_val, simpleRoot_zero, simpleRoot_one,
    positiveRootEquiv_val]

/-- A positive vector lies below itself. -/
theorem rootOrder_refl (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    RootOrder n hthree alpha alpha :=
  (rootOrder_indices alpha alpha).mpr (rootLE_refl n hthree alpha.index)

/-- Cone comparison of positive vectors is transitive. -/
theorem rootOrder_trans {n : ℕ} {hthree : 3 ≤ n} {alpha beta gamma : PositiveRoot n}
    (hfirst : RootOrder n hthree alpha beta) (hsecond : RootOrder n hthree beta gamma) :
    RootOrder n hthree alpha gamma :=
  (rootOrder_indices alpha gamma).mpr (rootLE_trans
    ((rootOrder_indices alpha beta).mp hfirst) ((rootOrder_indices beta gamma).mp hsecond))

/-- Two positive vectors below one another are equal. -/
theorem rootOrder_antisymm {n : ℕ} {hthree : 3 ≤ n} {alpha beta : PositiveRoot n}
    (hfirst : RootOrder n hthree alpha beta) (hsecond : RootOrder n hthree beta alpha) :
    alpha = beta :=
  (positiveRootEquiv n).symm.injective (rootLE_antisymm
    ((rootOrder_indices alpha beta).mp hfirst) ((rootOrder_indices beta alpha).mp hsecond))

/-- The positive-vector partial order defined by the real simple-root cone. -/
@[instance_reducible] def rootOrder (n : ℕ) (hthree : 3 ≤ n) :
    PartialOrder (PositiveRoot n) where
  le := RootOrder n hthree
  lt := fun alpha beta => RootOrder n hthree alpha beta ∧ ¬ RootOrder n hthree beta alpha
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_refl := rootOrder_refl n hthree
  le_trans := fun _ _ _ => rootOrder_trans
  le_antisymm := fun _ _ => rootOrder_antisymm

end Schubert.DihedralSplines
