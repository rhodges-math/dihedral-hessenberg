import Schubert.DihedralSplines.RootConjugateEdge
import Schubert.DihedralSplines.UpperConnectivity
import Schubert.Dihedral.LongestLength

/-! # Selected edges inside upper ideals -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Sufficiently high upper ideals contain all full-root internal endpoint edges. -/
theorem internal_full (ideal : HessenbergIdeal n hthree) (minimum : DihedralGroup n)
    (hlarge : 2 * (n - length n hthree minimum) < ideal.carrier.ncard)
    (source target : DihedralGroup n)
    (hsource : BruhatLE n hthree minimum source)
    (htarget : BruhatLE n hthree minimum target) :
    (source, target) ∈ ideal.toRootSubset.edges ↔
      (source, target) ∈ (RootSubset.full n).edges := by
  rw [RootSubset.mem_edges, RootSubset.mem_edges]
  constructor
  · rintro ⟨gamma, _, hneighbor⟩
    exact ⟨gamma, gamma.property, hneighbor⟩
  · rintro ⟨gamma, _, hneighbor⟩
    refine ⟨gamma, ideal.selected_of_short gamma ?_, hneighbor⟩
    change target = source * gamma.reflection at hneighbor
    let top := longestElement n hthree
    have hreflection : gamma.reflection = (top * source)⁻¹ * (top * target) := by
      rw [hneighbor]
      group
    have htriangle := (coxeterSystem n hthree).length_mul_le
      (top * source)⁻¹ (top * target)
    change length n hthree ((top * source)⁻¹ * (top * target)) ≤
      length n hthree (top * source)⁻¹ + length n hthree (top * target) at htriangle
    rw [← hreflection, length_inv] at htriangle
    have hsourceTop : length n hthree (top * source) = n - length n hthree source :=
      length_alternatingWord_top_mul n hthree source
    have htargetTop : length n hthree (top * target) = n - length n hthree target :=
      length_alternatingWord_top_mul n hthree target
    rw [hsourceTop, htargetTop] at htriangle
    have hsourceLength := bruhatLE_length_le n hthree hsource
    have htargetLength := bruhatLE_length_le n hthree htarget
    omega

/-- Internal selected-edge invariance implies constancy on a sufficiently high upper ideal. -/
theorem eq_on_upper (ideal : HessenbergIdeal n hthree) (minimum : DihedralGroup n)
    (hlarge : 2 * (n - length n hthree minimum) < ideal.carrier.ncard)
    {A : Sort*} (value : DihedralGroup n → A)
    (hinvariant : ∀ source target, BruhatLE n hthree minimum source →
      BruhatLE n hthree minimum target → (source, target) ∈ ideal.toRootSubset.edges →
        value source = value target) :
    ∀ vertex, BruhatLE n hthree minimum vertex → value vertex = value minimum := by
  apply RootSubset.eq_on_upper n hthree minimum value
  intro source target hsource htarget hedge
  exact hinvariant source target hsource htarget
    ((ideal.internal_full minimum hlarge source target hsource htarget).mpr hedge)

end Schubert.DihedralSplines.HessenbergIdeal
