import Schubert.Dihedral.RootReflectionVectors
import Schubert.Dihedral.RankTwoRootVectors
import Schubert.DihedralSplines.PaperFull

/-! # Connectivity of full-root upper ideals -/

namespace Schubert.Dihedral.RootSubset

/-- Every left root reflection gives a full-root endpoint edge. -/
theorem full_left_edge (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (vertex : DihedralGroup n) :
    (vertex, alpha.reflection * vertex) ∈ (full n).edges := by
  have hreflection := (alpha.isReflection hthree).conj vertex⁻¹
  rw [inv_inv] at hreflection
  obtain ⟨beta, hbeta⟩ := (isReflection_iff_positiveRoot n hthree _).mp hreflection
  apply ((full n).mem_edges _).mpr
  refine ⟨beta, beta.property, ?_⟩
  rw [hbeta]
  group

private theorem exists_simple_ascent (n : ℕ) (hthree : 3 ≤ n)
    (vertex : DihedralGroup n) (hne : vertex ≠ longestElement n hthree) :
    ∃ alpha : PositiveRoot n,
      Schubert.Dihedral.length n hthree (alpha.reflection * vertex) =
        Schubert.Dihedral.length n hthree vertex + 1 := by
  by_cases hone : vertex = 1
  · subst vertex
    refine ⟨simpleRoot n hthree 0, ?_⟩
    rw [mul_one, simpleRoot_reflection, length_simpleReflection, length_one]
  obtain ⟨alpha, halpha, _⟩ := unique_root_ascent n hthree vertex hone hne
  exact ⟨alpha, halpha.2⟩

/-- Functions invariant on internal full-root edges are constant on every Bruhat upper ideal. -/
theorem eq_top_on_upper (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    {A : Sort*} (value : DihedralGroup n → A)
    (hinvariant : ∀ source target, BruhatLE n hthree element source →
      BruhatLE n hthree element target → (source, target) ∈ (full n).edges →
        value source = value target) :
    ∀ vertex, BruhatLE n hthree element vertex →
      value vertex = value (longestElement n hthree) := by
  have htop : ∀ degree : ℕ, ∀ vertex : DihedralGroup n,
      n - Schubert.Dihedral.length n hthree vertex = degree → BruhatLE n hthree element vertex →
        value vertex = value (longestElement n hthree) := by
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree ih =>
      intro vertex hdegree hvertex
      by_cases heq : vertex = longestElement n hthree
      · exact congrArg value heq
      obtain ⟨alpha, hascent⟩ := exists_simple_ascent n hthree vertex heq
      have hvertexLength := bruhatLE_length_le n hthree hvertex
      have hnext : BruhatLE n hthree element (alpha.reflection * vertex) :=
        bruhatLE_of_length_lt n hthree (by omega)
      have hbound := length_le_polygon_parameter n hthree (alpha.reflection * vertex)
      have hless : n - Schubert.Dihedral.length n hthree (alpha.reflection * vertex) <
          degree := by omega
      exact (hinvariant vertex (alpha.reflection * vertex) hvertex hnext
        (full_left_edge n hthree alpha vertex)).trans
          (ih _ hless _ rfl hnext)
  intro vertex hvertex
  exact htop _ vertex rfl hvertex

/-- Internal-edge invariance makes every value on an upper ideal equal to its minimum value. -/
theorem eq_on_upper (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    {A : Sort*} (value : DihedralGroup n → A)
    (hinvariant : ∀ source target, BruhatLE n hthree element source →
      BruhatLE n hthree element target → (source, target) ∈ (full n).edges →
        value source = value target) :
    ∀ vertex, BruhatLE n hthree element vertex → value vertex = value element := by
  intro vertex hvertex
  exact (eq_top_on_upper n hthree element value hinvariant vertex hvertex).trans
    (eq_top_on_upper n hthree element value hinvariant element
      (bruhatLE_refl n hthree element)).symm

end Schubert.Dihedral.RootSubset
