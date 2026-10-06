import Schubert.Dihedral.RootDepth
import Schubert.Dihedral.SimpleRootObjects

/-! # Simple-reflection steps increasing root depth -/

namespace Schubert.Dihedral

/-- A positive-vector step by a simple reflection increasing the root depth by one. -/
def DepthStep {n : ℕ} (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) : Prop :=
  ∃ simple : PositiveRoot n,
    (simple = simpleRoot n hthree 0 ∨ simple = simpleRoot n hthree 1) ∧
      realAction n simple.reflection alpha.val = beta.val ∧
        beta.depth hthree = alpha.depth hthree + 1

end Schubert.Dihedral
