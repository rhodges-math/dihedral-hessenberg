import Schubert.DihedralSplines.ChamberRootOrder
import Schubert.DihedralSplines.HessenbergVectorClassification

/-! # Hessenberg ideal transport through generic root chambers -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Every cone ideal in a generic chamber is the image of a canonical cone ideal. -/
theorem chamber_ideal {n : ℕ} [NeZero n] {data : Separator n}
    (frame : data.Frame) (hthree : 3 ≤ n) (selected : Set RealPlane)
    (hpositive : selected ⊆ data.positive)
    (hlower : ∀ alpha beta : data.Positive,
      (∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
        beta.val - alpha.val = first • (frame.first hthree).val +
          second • (frame.second hthree).val) →
      beta.val ∈ selected → alpha.val ∈ selected)
    (hfirst : (frame.first hthree).val ∈ selected)
    (hsecond : (frame.second hthree).val ∈ selected) :
    ∃ ideal : HessenbergIdeal n hthree,
      selected = realAction n frame.element '' ideal.carrier ∧
        selected.ncard = ideal.carrier.ncard := by
  let ideal : HessenbergIdeal n hthree :=
    { carrier := {vector | vector ∈ positiveRoots n ∧
          realAction n frame.element vector ∈ selected}
      positive := fun _ hmem => hmem.1
      lower := by
        intro alpha beta horder hbeta
        refine ⟨alpha.property, ?_⟩
        exact hlower (frame.root alpha) (frame.root beta)
          ((chamber_order frame hthree alpha beta).mpr horder) hbeta.2
      first_mem := ⟨(simpleRoot n hthree 0).property, hfirst⟩
      second_mem := ⟨(simpleRoot n hthree 1).property, hsecond⟩ }
  have himage : selected = realAction n frame.element '' ideal.carrier := by
    ext vector
    constructor
    · intro hvector
      have hpos := hpositive hvector
      rw [frame.image] at hpos
      obtain ⟨original, horiginal, heq⟩ := hpos
      exact ⟨original, ⟨horiginal, heq ▸ hvector⟩, heq⟩
    · rintro ⟨original, horiginal, rfl⟩
      exact horiginal.2
  refine ⟨ideal, himage, ?_⟩
  rw [himage]
  exact Set.ncard_image_of_injective ideal.carrier (realLinearEquiv n frame.element).injective

end Schubert.DihedralSplines
