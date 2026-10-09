import DihedralHessenberg.Dihedral.ReflectionIndex
import DihedralHessenberg.Dihedral.RootObjects

/-! # A six-root reflection-subset obstruction to chamber transport -/

namespace Schubert.Dihedral

private theorem six_reflection_obstruction :
    ∀ element : DihedralGroup 6,
      ({.sr 0, .sr 1, .sr 2, .sr 4} : Finset (DihedralGroup 6)) ≠
        ({.sr 0, .sr 1, .sr 5, .sr 2} : Finset (DihedralGroup 6)).image
          (fun reflection => element * reflection * element⁻¹) := by
  decide

/-- The four selected six-root reflections are no translate of the four-root cone ideal. -/
theorem six_reflection_subset (element : DihedralGroup 6) :
    ({(positiveRootEquiv 6 ⟨0, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨1, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨3, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨4, by decide⟩).reflection} : Finset (DihedralGroup 6)) ≠
    ({(positiveRootEquiv 6 ⟨0, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨1, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨2, by decide⟩).reflection,
      (positiveRootEquiv 6 ⟨3, by decide⟩).reflection} : Finset (DihedralGroup 6)).image
        (fun reflection => element * reflection * element⁻¹) := by
  simp only [PositiveRoot.reflection_equiv]
  have hroot (index : Fin 6) : rootReflection index =
      ![DihedralGroup.sr 0, .sr 1, .sr 5, .sr 2, .sr 4, .sr 3] index := by
    fin_cases index
    all_goals first | rw [rootReflection_eq_sr_of_even _ (by decide)] |
      rw [rootReflection_eq_sr_of_odd _ (by decide)]
    all_goals decide
  simp only [hroot]
  exact six_reflection_obstruction element

end Schubert.Dihedral
