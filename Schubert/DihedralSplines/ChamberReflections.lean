import Schubert.DihedralSplines.ChamberIdeal

/-! # Reflection carriers of translated positive subsets -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Chamber reflection carriers transform by conjugation under the action. -/
theorem chamber_reflections {n : ℕ} {data : Separator n}
    (frame : data.Frame) (hthree : 3 ≤ n) (selected : Set RealPlane)
    (ideal : HessenbergIdeal n hthree)
    (himage : selected = realAction n frame.element '' ideal.carrier) :
    (fun alpha : data.Positive => (data.reflectionEquiv hthree alpha).val) ''
        {alpha : data.Positive | alpha.val ∈ selected} =
      (fun reflection => frame.element * reflection * frame.element⁻¹) ''
        (PositiveRoot.reflection '' {alpha : PositiveRoot n | alpha.val ∈ ideal.carrier}) := by
  ext reflection
  constructor
  · rintro ⟨alpha, halpha, rfl⟩
    rw [himage] at halpha
    obtain ⟨vector, hvector, heq⟩ := halpha
    let original : PositiveRoot n := ⟨vector, ideal.positive hvector⟩
    have halpha_eq : alpha = frame.root original := Subtype.ext heq.symm
    rw [halpha_eq]
    change (data.reflectionEquiv hthree (frame.root original)).val ∈ _
    rw [frame.reflection_root]
    exact ⟨original.reflection, ⟨original, hvector, rfl⟩, rfl⟩
  · rintro ⟨originalReflection, ⟨original, horiginal, rfl⟩, rfl⟩
    refine ⟨frame.root original, ?_, frame.reflection_root hthree original⟩
    rw [himage]
    exact ⟨original.val, horiginal, rfl⟩

end Schubert.DihedralSplines
