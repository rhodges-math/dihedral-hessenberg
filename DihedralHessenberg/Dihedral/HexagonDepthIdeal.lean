import DihedralHessenberg.Dihedral.HexagonDepth
import DihedralHessenberg.Dihedral.HexagonReflectionSubset
import DihedralHessenberg.Dihedral.RootDepthOrder

/-! # A depth-order lower subset of the six root vectors -/

namespace Schubert.Dihedral

/-- The six-root subset containing the first, second, fourth and fifth vectors. -/
def sixLowerRoots : Set RealPlane :=
  {(positiveRootEquiv 6 ⟨0, by decide⟩).val, (positiveRootEquiv 6 ⟨1, by decide⟩).val,
    (positiveRootEquiv 6 ⟨3, by decide⟩).val, (positiveRootEquiv 6 ⟨4, by decide⟩).val}

private theorem six_lower_mem (index : Fin 6) :
    (positiveRootEquiv 6 index).val ∈ sixLowerRoots ↔
      index.val = 0 ∨ index.val = 1 ∨ index.val = 3 ∨ index.val = 4 := by
  simp only [sixLowerRoots, Set.mem_insert_iff, Set.mem_singleton_iff,
    positiveRootEquiv_val, (positiveRoot_injective 6).eq_iff, Fin.ext_iff]

/-- The four vectors are lower under every increasing-depth simple-reflection step. -/
theorem six_depth_lower (alpha beta : PositiveRoot 6)
    (hstep : DepthStep (by decide) alpha beta) (hbeta : beta.val ∈ sixLowerRoots) :
    alpha.val ∈ sixLowerRoots := by
  obtain ⟨index, rfl⟩ := (positiveRootEquiv 6).surjective alpha
  obtain ⟨target, rfl⟩ := (positiveRootEquiv 6).surjective beta
  obtain ⟨simple, hsimple, haction, hdepth⟩ := hstep
  have hconjugate := PositiveRoot.signed_conjugation simple.reflection
    (positiveRootEquiv 6 index) (positiveRootEquiv 6 target) (Or.inl haction)
  rw [six_depth, six_depth] at hdepth
  rw [six_lower_mem] at hbeta ⊢
  rcases hsimple with rfl | rfl
  all_goals fin_cases index <;> fin_cases target
  all_goals norm_num at hdepth
  all_goals norm_num at hbeta
  all_goals norm_num
  all_goals
    simp only [simpleRoot_reflection, PositiveRoot.reflection_equiv,
      rootReflection_eq_sr_neg_angularIndex] at hconjugate
    revert hconjugate
    decide

/-- The four vectors are a lower subset for the reflexive transitive depth-step order. -/
theorem six_depth_lower_paths (alpha beta : PositiveRoot 6)
    (hpath : Relation.ReflTransGen (DepthStep (by decide)) alpha beta)
    (hbeta : beta.val ∈ sixLowerRoots) : alpha.val ∈ sixLowerRoots := by
  revert hbeta
  induction hpath with
  | refl => exact fun hmem => hmem
  | @tail intermediate terminal hpath hstep induction =>
    intro hterminal
    exact induction (six_depth_lower intermediate terminal hstep hterminal)

end Schubert.Dihedral
