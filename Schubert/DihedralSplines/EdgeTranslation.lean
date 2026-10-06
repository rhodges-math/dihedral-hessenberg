import Schubert.DihedralSplines.PaperGraph

/-! # Translation of geometric reflection endpoints -/

namespace Schubert.Dihedral.RootSubset

/-- Left translation preserves the selected endpoint graph. -/
theorem translate_edge {n : ℕ} (selected : RootSubset n)
    (translate source target : DihedralGroup n) :
    (translate * source, translate * target) ∈ selected.edges ↔
      (source, target) ∈ selected.edges := by
  rw [selected.mem_edges, selected.mem_edges]
  constructor
  · rintro ⟨alpha, hselected, heq⟩
    refine ⟨alpha, hselected, ?_⟩
    apply mul_left_cancel (a := translate)
    simpa only [mul_assoc] using heq
  · rintro ⟨alpha, hselected, heq⟩
    refine ⟨alpha, hselected, ?_⟩
    simpa only [mul_assoc] using congrArg (fun current => translate * current) heq

end Schubert.Dihedral.RootSubset
