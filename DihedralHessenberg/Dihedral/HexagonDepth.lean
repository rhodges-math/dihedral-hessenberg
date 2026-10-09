import DihedralHessenberg.Dihedral.RootDepth
import DihedralHessenberg.Dihedral.SimpleRootPermutation
import DihedralHessenberg.Dihedral.RootObjectAction
import DihedralHessenberg.Dihedral.RootReflectionAngles
import DihedralHessenberg.Dihedral.RootNormal

/-! # Six-root depths and simple-reflection steps -/

namespace Schubert.Dihedral

private def sixWitness : Fin 6 → DihedralGroup 6 :=
  ![.sr 0, .sr 1, .r (-1), .r 1, .sr (-1), .sr 2]

/-- The six positive vectors have depths one, one, two, two, three and three. -/
theorem six_depth (index : Fin 6) :
    (positiveRootEquiv 6 index).depth (by decide) = index.val / 2 + 1 := by
  have hlower := (positiveRootEquiv 6 index).layer_le_depth (by decide)
  rw [PositiveRoot.index_equiv] at hlower
  apply Nat.le_antisymm _ hlower
  have hinversion : index ∈ rightInversions 6 (by decide) (sixWitness index) := by
    fin_cases index
    · change (⟨0, by decide⟩ : Fin 6) ∈ rightInversions 6 (by decide) (.sr 0)
      rw [mem_rightInversions_sr_iff]
      decide
    · change (⟨1, by decide⟩ : Fin 6) ∈ rightInversions 6 (by decide) (.sr 1)
      rw [mem_rightInversions_sr_iff]
      decide
    · change (⟨2, by decide⟩ : Fin 6) ∈ rightInversions 6 (by decide) (.r (-1))
      rw [mem_rightInversions_r_iff]
      decide
    · change (⟨3, by decide⟩ : Fin 6) ∈ rightInversions 6 (by decide) (.r 1)
      rw [mem_rightInversions_r_iff]
      decide
    · change (⟨4, by decide⟩ : Fin 6) ∈ rightInversions 6 (by decide) (.sr (-1))
      rw [mem_rightInversions_sr_iff]
      decide
    · change (⟨5, by decide⟩ : Fin 6) ∈ rightInversions 6 (by decide) (.sr 2)
      rw [mem_rightInversions_sr_iff]
      decide
  have hnegative := ((mem_rightInversionSet 6 (by decide) (sixWitness index) index).mpr
    hinversion).2
  have hbound := (positiveRootEquiv 6 index).depth_le (by decide) (sixWitness index) hnegative
  have hlength : length 6 (by decide) (sixWitness index) = index.val / 2 + 1 := by
    fin_cases index
    · change length 6 (by decide) (.sr 0) = 1
      rw [length_sr]
      decide
    · change length 6 (by decide) (.sr 1) = 1
      rw [length_sr]
      decide
    · change length 6 (by decide) (.r (-1)) = 2
      rw [length_r]
      decide
    · change length 6 (by decide) (.r 1) = 2
      rw [length_r]
      decide
    · change length 6 (by decide) (.sr (-1)) = 3
      rw [length_sr]
      decide
    · change length 6 (by decide) (.sr 2) = 3
      rw [length_sr]
      decide
  exact hlength ▸ hbound

private theorem simple_image (simple : Fin 2) (alpha beta : PositiveRoot 6)
    (hne : alpha ≠ simpleRoot 6 (by decide) simple)
    (hconjugate : (simpleRoot 6 (by decide) simple).reflection * alpha.reflection *
      (simpleRoot 6 (by decide) simple).reflection⁻¹ = beta.reflection) :
    realAction 6 (simpleRoot 6 (by decide) simple).reflection alpha.val = beta.val := by
  have hval : alpha.val ≠ (simpleRoot 6 (by decide) simple).val :=
    fun heq => hne (Subtype.ext heq)
  have himage := (simple_except_bijOn 6 (by decide) simple).mapsTo
    ⟨alpha.property, by simpa only [Set.mem_singleton_iff] using hval⟩
  let image : PositiveRoot 6 :=
    ⟨realAction 6 (simpleRoot 6 (by decide) simple).reflection alpha.val, himage.1⟩
  have hreflection := PositiveRoot.signed_conjugation
    (simpleRoot 6 (by decide) simple).reflection alpha image (Or.inl rfl)
  exact congrArg Subtype.val (PositiveRoot.reflection_injective 6
    (hreflection.trans hconjugate))

private def sixTarget (simple : Fin 2) : Fin 6 → Fin 6 :=
  if simple = 0 then ![0, 2, 1, 4, 3, 5] else ![3, 1, 5, 0, 4, 2]

/-- Simple reflections have the six-root action table away from their own normal. -/
theorem six_simple_action (simple : Fin 2) (index : Fin 6) (hne : index.val ≠ simple.val) :
    realAction 6 (simpleRoot 6 (by decide) simple).reflection
      (positiveRootEquiv 6 index).val = (positiveRootEquiv 6 (sixTarget simple index)).val := by
  apply simple_image simple
  · intro heq
    have hindex := congrArg PositiveRoot.index heq
    rw [PositiveRoot.index_equiv] at hindex
    fin_cases simple
    · change index = (simpleRoot 6 (by decide) 0).index at hindex
      rw [simpleRoot_zero, PositiveRoot.index_equiv] at hindex
      exact hne (congrArg Fin.val hindex)
    · change index = (simpleRoot 6 (by decide) 1).index at hindex
      rw [simpleRoot_one, PositiveRoot.index_equiv] at hindex
      exact hne (congrArg Fin.val hindex)
  · rw [simpleRoot_reflection, PositiveRoot.reflection_equiv,
      PositiveRoot.reflection_equiv, rootReflection_eq_sr_neg_angularIndex,
      rootReflection_eq_sr_neg_angularIndex]
    fin_cases simple
    · fin_cases index
      all_goals simp only [sixTarget]
      all_goals decide
    · fin_cases index
      all_goals simp only [sixTarget]
      all_goals decide

end Schubert.Dihedral
