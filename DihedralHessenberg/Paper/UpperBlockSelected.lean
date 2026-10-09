import DihedralHessenberg.Dihedral.UpperBlock
import DihedralHessenberg.Paper.HessenbergUpper
import DihedralHessenberg.Paper.HessenbergBlock

/-! # Selected terminal reflections of upper alternating blocks -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal.Upper

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} {ideal : HessenbergIdeal n hthree}

/-- Every reflection from the minimum into its upper ideal is selected. -/
theorem selected_reflection (upper : Upper ideal) (alpha : PositiveRoot n)
    (htarget : BruhatLE n hthree upper.minimum (upper.minimum * alpha.reflection)) :
    alpha.val ∈ ideal := by
  have hfull : (upper.minimum, upper.minimum * alpha.reflection) ∈ (RootSubset.full n).edges :=
    ⟨alpha, alpha.property, rfl⟩
  have hselected := (upper.star_full _ htarget).mpr hfull
  obtain ⟨beta, hbeta, heq⟩ := (ideal.toRootSubset.mem_edges _).mp hselected
  change upper.minimum * alpha.reflection = upper.minimum * beta.reflection at heq
  have hroot := PositiveRoot.reflection_injective n (mul_left_cancel heq)
  rw [hroot]
  exact hbeta

/-- The terminal vector of a high-half first-root upper block is selected. -/
theorem first_terminal (upper : Upper ideal)
    (hascent : length n hthree (upper.minimum * (simpleRoot n hthree 0).reflection) =
      length n hthree upper.minimum + 1)
    (hhalf : n < 2 * length n hthree upper.minimum + 1) :
    (positiveRootEquiv n ⟨2 * (n - length n hthree upper.minimum - 1), by
      have := length_le_polygon_parameter n hthree
        (upper.minimum * (simpleRoot n hthree 0).reflection)
      omega⟩).val ∈ ideal := by
  let half := n - length n hthree upper.minimum - 1
  have hbound := length_le_polygon_parameter n hthree
    (upper.minimum * (simpleRoot n hthree 0).reflection)
  have hreflection : (positiveRootEquiv n ⟨2 * half, by dsimp only [half]; omega⟩).reflection =
      (simpleRoot n hthree 0).alternatingProduct (simpleRoot n hthree 1) (2 * half + 1) := by
    rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
      simpleReflection_zero, simpleReflection_one]
    exact numbered_even_reflection n half (by dsimp only [half]; omega)
  apply upper.selected_reflection
  rw [hreflection]
  have hset := alternatingBlock_upper upper.minimum (simpleRoot n hthree 0)
    (simpleRoot n hthree 1) (Or.inl ⟨rfl, rfl⟩) hascent hhalf
  apply hset.subset
  exact (mem_alternatingBlock _ _ _ _ _).mpr ⟨2 * half + 1, by omega, rfl⟩

/-- The terminal vector of a high-half second-root upper block is selected. -/
theorem second_terminal (upper : Upper ideal)
    (hascent : length n hthree (upper.minimum * (simpleRoot n hthree 1).reflection) =
      length n hthree upper.minimum + 1)
    (hhalf : n < 2 * length n hthree upper.minimum + 1) :
    (positiveRootEquiv n ⟨2 * (n - length n hthree upper.minimum - 1) + 1, by
      have := length_le_polygon_parameter n hthree
        (upper.minimum * (simpleRoot n hthree 1).reflection)
      omega⟩).val ∈ ideal := by
  let half := n - length n hthree upper.minimum - 1
  have hbound := length_le_polygon_parameter n hthree
    (upper.minimum * (simpleRoot n hthree 1).reflection)
  have hreflection : (positiveRootEquiv n ⟨2 * half + 1, by dsimp only [half]; omega⟩).reflection =
      (simpleRoot n hthree 1).alternatingProduct (simpleRoot n hthree 0) (2 * half + 1) := by
    rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection,
      simpleReflection_one, simpleReflection_zero]
    exact numbered_odd_reflection n half (by dsimp only [half]; omega)
  apply upper.selected_reflection
  rw [hreflection]
  have hset := alternatingBlock_upper upper.minimum (simpleRoot n hthree 1)
    (simpleRoot n hthree 0) (Or.inr ⟨rfl, rfl⟩) hascent hhalf
  apply hset.subset
  exact (mem_alternatingBlock _ _ _ _ _).mpr ⟨2 * half + 1, by omega, rfl⟩


/-- A nonterminal high-half upper ideal is a selected-terminal alternating block. -/
theorem exists_block (upper : Upper ideal)
    (hneTop : upper.minimum ≠ longestElement n hthree)
    (hhalf : n < 2 * length n hthree upper.minimum + 1) :
    ∃ block : Block ideal, block.base = upper.minimum ∧
      block.half = n - length n hthree upper.minimum - 1 ∧
      (block.vertices : Set (DihedralGroup n)) =
        {target | BruhatLE n hthree upper.minimum target} := by
  have hpositive : 0 < length n hthree upper.minimum := by omega
  have hneOne : upper.minimum⁻¹ ≠ 1 := by
    rw [inv_ne_one]
    exact (length_pos_iff_ne_one n hthree _).mp hpositive
  have hneInvTop : upper.minimum⁻¹ ≠ longestElement n hthree := by
    intro heq
    apply hneTop
    apply (length_eq_longest n hthree _).mp
    rw [← length_inv n hthree upper.minimum, heq]
    exact (length_eq_longest n hthree _).mpr rfl
  obtain ⟨alpha, ⟨hsimple, hascent⟩, _⟩ :=
    unique_root_ascent n hthree upper.minimum⁻¹ hneOne hneInvTop
  have hright : length n hthree (upper.minimum * alpha.reflection) =
      length n hthree upper.minimum + 1 := by
    have hinv : alpha.reflection * upper.minimum⁻¹ =
        (upper.minimum * alpha.reflection)⁻¹ := by
      rw [mul_inv_rev, PositiveRoot.reflection_inv]
    rw [hinv, length_inv, length_inv] at hascent
    exact hascent
  have hbound := length_le_polygon_parameter n hthree (upper.minimum * alpha.reflection)
  rcases hsimple with hfirst | hsecond
  · subst alpha
    refine ⟨Block.first ideal upper.minimum (n - length n hthree upper.minimum - 1)
      (by omega) (upper.first_terminal hright hhalf), rfl, rfl, ?_⟩
    exact alternatingBlock_upper upper.minimum _ _ (Or.inl ⟨rfl, rfl⟩) hright hhalf
  · subst alpha
    refine ⟨Block.second ideal upper.minimum (n - length n hthree upper.minimum - 1)
      (by omega) (upper.second_terminal hright hhalf), rfl, rfl, ?_⟩
    exact alternatingBlock_upper upper.minimum _ _ (Or.inr ⟨rfl, rfl⟩) hright hhalf

end Schubert.DihedralSplines.HessenbergIdeal.Upper

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- A selected high-half simple ascent has exactly the displayed alternating-block support. -/
theorem ascent_block {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (vertex : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ∃ block : Block ideal, block.base = vertex ∧
      block.half = n - length n hthree vertex - 1 ∧
      (block.vertices : Set (DihedralGroup n)) = {target | BruhatLE n hthree vertex target} := by
  let upper := Upper.ofAscent ideal alpha hsimple vertex hascent hhalf hedge
  have hneTop : vertex ≠ longestElement n hthree := by
    intro heq
    have hlength := (length_eq_longest n hthree vertex).mpr heq
    have hbound := length_le_polygon_parameter n hthree (alpha.reflection * vertex)
    omega
  exact upper.exists_block hneTop hhalf

end Schubert.DihedralSplines.HessenbergIdeal
