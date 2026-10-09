import DihedralHessenberg.Dihedral.RootInversionDescent
import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Dihedral.GeometricAscent

/-! # Geometric inversion-set updates at simple ascents -/

namespace Schubert.Dihedral

/-- A simple left ascent inserts the positive inverse image into right inversions. -/
theorem rightInversionSet_ascent (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2)
    (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    realAction n element⁻¹ (simpleRoot n hthree simple).val ∈ positiveRoots n ∧
      rightInversionSet n (simpleReflection n simple * element) =
        insert (realAction n element⁻¹ (simpleRoot n hthree simple).val)
          (rightInversionSet n element) ∧
      realAction n element⁻¹ (simpleRoot n hthree simple).val ∉ rightInversionSet n element := by
  classical
  let alpha := simpleRoot n hthree simple
  have hreflection : rootReflection alpha.index = simpleReflection n simple :=
    simpleRoot_reflection n hthree simple
  obtain ⟨image, himage, hset, hnot⟩ :=
    _root_.Schubert.Dihedral.IndexedInversions.right_ascent_image
    n hthree simple alpha.index element hreflection hascent
  have hreal : realAction n element⁻¹ alpha.val = positiveRoot n image := by
    apply PositiveRoot.image_eq element⁻¹ alpha (positiveRootEquiv n image)
    simpa only [complexPositiveRoot, alpha.index_val, positiveRootEquiv_val] using himage
  refine ⟨?_, ?_, ?_⟩
  · rw [hreal]
    exact ⟨image, rfl⟩
  · rw [← image_rightInversions n hthree (simpleReflection n simple * element),
      hset, Finset.coe_insert, Set.image_insert_eq, image_rightInversions, hreal]
  · rw [hreal, mem_rightInversionSet]
    exact hnot

/-- A simple left ascent inserts its vector and acts on the old left inversion vectors. -/
theorem leftInversionSet_ascent (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2)
    (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    leftInversionSet n (simpleReflection n simple * element) =
      insert (simpleRoot n hthree simple).val
        (realAction n (simpleReflection n simple) '' leftInversionSet n element) := by
  let alpha := simpleRoot n hthree simple
  have hreflection : rootReflection alpha.index = simpleReflection n simple :=
    simpleRoot_reflection n hthree simple
  ext vector
  constructor
  · intro hmem
    obtain ⟨index, rfl⟩ := hmem.1
    have hindex := (mem_leftInversionSet n hthree _ index).mp hmem
    rcases (_root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem n hthree simple alpha.index
      element hreflection hascent index).mp hindex with heq | ⟨previous, hprevious, himage⟩
    · exact Or.inl (heq ▸ alpha.index_val)
    · refine Or.inr ⟨positiveRoot n previous,
        (mem_leftInversionSet n hthree element previous).mpr hprevious, ?_⟩
      apply PositiveRoot.image_eq (simpleReflection n simple)
        (positiveRootEquiv n previous) (positiveRootEquiv n index)
      exact himage
  · rintro (rfl | ⟨_, hprevious, heq⟩)
    · rw [← alpha.index_val, mem_leftInversionSet]
      exact (_root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem n hthree simple alpha.index
        element hreflection hascent alpha.index).mpr (Or.inl rfl)
    · obtain ⟨previous, rfl⟩ := hprevious.1
      have hpreviousIndex := (mem_leftInversionSet n hthree element previous).mp hprevious
      obtain ⟨image, himage, _⟩ := _root_.Schubert.Dihedral.IndexedInversions.simple_image_of_ascent
        n hthree simple alpha.index element hreflection hascent previous hpreviousIndex
      have hreal : realAction n (simpleReflection n simple) (positiveRoot n previous) =
          positiveRoot n image := PositiveRoot.image_eq (simpleReflection n simple)
            (positiveRootEquiv n previous) (positiveRootEquiv n image) himage
      have hvector : positiveRoot n image = vector := hreal.symm.trans heq
      rw [← hvector, mem_leftInversionSet]
      exact (_root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem n hthree simple alpha.index
        element hreflection hascent image).mpr (Or.inr ⟨previous, hpreviousIndex, himage⟩)

/-- The newly inserted simple vector is disjoint from the transformed old left inversions. -/
theorem leftInversionSet_ascent_disjoint (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2)
    (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    (simpleRoot n hthree simple).val ∉
      realAction n (simpleReflection n simple) '' leftInversionSet n element := by
  let : NeZero n := ⟨by omega⟩
  rintro ⟨vector, hvector, heq⟩
  let beta : PositiveRoot n := ⟨vector, hvector.1⟩
  have hconj := PositiveRoot.signed_conjugation (simpleReflection n simple) beta
    (simpleRoot n hthree simple) (Or.inl heq)
  have hreflection : beta.reflection = simpleReflection n simple := by
    calc
      beta.reflection = (simpleReflection n simple)⁻¹ *
        (simpleReflection n simple * beta.reflection * (simpleReflection n simple)⁻¹) *
          simpleReflection n simple := by group
      _ = (simpleReflection n simple)⁻¹ * (simpleRoot n hthree simple).reflection *
          simpleReflection n simple := by rw [← hconj]
      _ = simpleReflection n simple := by rw [simpleRoot_reflection]; group
  have hlt := (PositiveRoot.left_descent hthree element beta).mp hvector
  rw [hreflection, hascent] at hlt
  omega

end Schubert.Dihedral
