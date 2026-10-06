import Schubert.Dihedral.RootLatticeRescaling
import Schubert.Dihedral.A2Roots
import Schubert.DihedralSplines.HessenbergVectorClassification

/-! # Integer root comparisons in the numbered radial configurations -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private def bCoefficients : Fin 4 → ℕ × ℕ := ![(1, 0), (0, 1), (2, 1), (1, 1)]
private def cCoefficients : Fin 4 → ℕ × ℕ := ![(1, 0), (0, 1), (1, 1), (1, 2)]
private def gCoefficients : Fin 6 → ℕ × ℕ :=
  ![(1, 0), (0, 1), (3, 1), (1, 1), (2, 1), (3, 2)]

private theorem b_coefficients (index : PositiveRootIndex 4) :
    PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 index) •
      positiveRoot 4 index =
        ((bCoefficients index).1 : ℝ) • RootLattice.b2.first +
          ((bCoefficients index).2 : ℝ) • RootLattice.b2.second := by
  rw [RootLattice.b2_numbered]
  fin_cases index <;> norm_num [bCoefficients]

/-- Integer comparison of the B2 radial vectors is coordinatewise comparison. -/
private theorem b2_comparison (first second : PositiveRootIndex 4) :
    RootLattice.b2.LE
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 first) •
        positiveRoot 4 first)
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 second) •
        positiveRoot 4 second) ↔
      (bCoefficients first).1 ≤ (bCoefficients second).1 ∧
        (bCoefficients first).2 ≤ (bCoefficients second).2 := by
  rw [b_coefficients, b_coefficients,
    RootLattice.le_coefficients _ RootLattice.b2_independent]

private theorem c_coefficients (index : PositiveRootIndex 4) :
    PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 index) •
      positiveRoot 4 index =
        ((cCoefficients index).1 : ℝ) • RootLattice.c2.first +
          ((cCoefficients index).2 : ℝ) • RootLattice.c2.second := by
  rw [RootLattice.c2_numbered]
  fin_cases index <;> norm_num [cCoefficients]

/-- Integer comparison of the C2 radial vectors is coordinatewise comparison. -/
private theorem c2_comparison (first second : PositiveRootIndex 4) :
    RootLattice.c2.LE
      (PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 first) •
        positiveRoot 4 first)
      (PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 second) •
        positiveRoot 4 second) ↔
      (cCoefficients first).1 ≤ (cCoefficients second).1 ∧
        (cCoefficients first).2 ≤ (cCoefficients second).2 := by
  rw [c_coefficients, c_coefficients,
    RootLattice.le_coefficients _ RootLattice.c2_independent]

private theorem g_coefficients (index : PositiveRootIndex 6) :
    PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 index) •
      positiveRoot 6 index =
        ((gCoefficients index).1 : ℝ) • RootLattice.g2.first +
          ((gCoefficients index).2 : ℝ) • RootLattice.g2.second := by
  rw [RootLattice.g2_numbered]
  fin_cases index <;> norm_num [gCoefficients]

/-- Integer comparison of the G2 radial vectors is coordinatewise comparison. -/
private theorem g2_comparison (first second : PositiveRootIndex 6) :
    RootLattice.g2.LE
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 first) •
        positiveRoot 6 first)
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 second) •
        positiveRoot 6 second) ↔
      (gCoefficients first).1 ≤ (gCoefficients second).1 ∧
        (gCoefficients first).2 ≤ (gCoefficients second).2 := by
  rw [g_coefficients, g_coefficients,
    RootLattice.le_coefficients _ RootLattice.g2_independent]

private theorem b_flags (first second : Fin 4) :
    (bCoefficients first).1 ≤ (bCoefficients second).1 ∧
      (bCoefficients first).2 ≤ (bCoefficients second).2 ↔
    first = second ∨ first.val / 2 < second.val / 2 ∨ first.val = 3 ∧ second.val = 2 := by
  fin_cases first <;> fin_cases second <;> norm_num [bCoefficients]

private theorem c_flags (first second : Fin 4) :
    (cCoefficients first).1 ≤ (cCoefficients second).1 ∧
      (cCoefficients first).2 ≤ (cCoefficients second).2 ↔
    first = second ∨ first.val / 2 < second.val / 2 ∨ first.val = 2 ∧ second.val = 3 := by
  fin_cases first <;> fin_cases second <;> norm_num [cCoefficients]

/-- The B and C lattice orders differ on the same positive unit directions. -/
theorem four_orders_differ :
    ∃ alpha beta : PositiveRoot 4,
      RootLattice.b2.LE (RootLattice.b2Rescaling.equiv alpha).val
        (RootLattice.b2Rescaling.equiv beta).val ∧
      ¬ RootLattice.c2.LE (RootLattice.c2Rescaling.equiv alpha).val
        (RootLattice.c2Rescaling.equiv beta).val := by
  refine ⟨positiveRootEquiv 4 ⟨3, by decide⟩, positiveRootEquiv 4 ⟨2, by decide⟩, ?_⟩
  change RootLattice.b2.LE
    (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 ⟨3, by decide⟩) •
      positiveRoot 4 ⟨3, by decide⟩)
    (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 ⟨2, by decide⟩) •
      positiveRoot 4 ⟨2, by decide⟩) ∧
    ¬ RootLattice.c2.LE
    (PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 ⟨3, by decide⟩) •
      positiveRoot 4 ⟨3, by decide⟩)
    (PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 ⟨2, by decide⟩) •
      positiveRoot 4 ⟨2, by decide⟩)
  rw [b2_comparison, c2_comparison]
  norm_num [bCoefficients, cCoefficients]

/-- Every lower subset of four unit directions is a B or C lower ideal after radial transport. -/
theorem four_lower_ideals (selected : RootSubset 4)
    (hlower : ∀ alpha beta : PositiveRoot 4, RootOrder 4 (by decide) alpha beta →
      beta.val ∈ selected → alpha.val ∈ selected) :
    RootLattice.b2.Lower (RootLattice.b2Rescaling.image selected.carrier) ∨
      RootLattice.c2.Lower (RootLattice.c2Rescaling.image selected.carrier) := by
  by_cases hthird : positiveRoot 4 ⟨2, by decide⟩ ∈ selected
  · right
    refine ⟨RootLattice.c2Rescaling.image_subset _, ?_⟩
    intro source target hsource htarget hle hselected
    rw [RootLattice.c2Rescaling.carrier] at hsource htarget
    obtain ⟨alpha, rfl⟩ := hsource
    obtain ⟨beta, rfl⟩ := htarget
    have hbeta := (RootLattice.c2Rescaling.mem_image selected.carrier beta).mp hselected
    apply (RootLattice.c2Rescaling.mem_image selected.carrier alpha).mpr
    obtain ⟨first, rfl⟩ := (positiveRootEquiv 4).surjective alpha
    obtain ⟨second, rfl⟩ := (positiveRootEquiv 4).surjective beta
    change RootLattice.c2.LE
      (PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 first) •
        positiveRoot 4 first)
      (PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1 (positiveRootEquiv 4 second) •
        positiveRoot 4 second) at hle
    rw [c2_comparison, c_flags] at hle
    rcases hle with hequal | hlayer | hextra
    · subst second
      exact hbeta
    · apply hlower _ _ _ hbeta
      rw [rootOrder_layers, PositiveRoot.index_equiv, PositiveRoot.index_equiv]
      exact Or.inr hlayer
    · have hequal : first = ⟨2, by decide⟩ := Fin.ext hextra.1
      subst first
      exact hthird
  · left
    refine ⟨RootLattice.b2Rescaling.image_subset _, ?_⟩
    intro source target hsource htarget hle hselected
    rw [RootLattice.b2Rescaling.carrier] at hsource htarget
    obtain ⟨alpha, rfl⟩ := hsource
    obtain ⟨beta, rfl⟩ := htarget
    have hbeta := (RootLattice.b2Rescaling.mem_image selected.carrier beta).mp hselected
    apply (RootLattice.b2Rescaling.mem_image selected.carrier alpha).mpr
    obtain ⟨first, rfl⟩ := (positiveRootEquiv 4).surjective alpha
    obtain ⟨second, rfl⟩ := (positiveRootEquiv 4).surjective beta
    change RootLattice.b2.LE
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 first) •
        positiveRoot 4 first)
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2) (positiveRootEquiv 4 second) •
        positiveRoot 4 second) at hle
    rw [b2_comparison, b_flags] at hle
    rcases hle with hequal | hlayer | hextra
    · subst second
      exact hbeta
    · apply hlower _ _ _ hbeta
      rw [rootOrder_layers, PositiveRoot.index_equiv, PositiveRoot.index_equiv]
      exact Or.inr hlayer
    · have hequal : second = ⟨2, by decide⟩ := Fin.ext hextra.2
      subst second
      exact False.elim (hthird hbeta)

/-- A lower subset of the six unit directions can fail to be a G2 lower ideal. -/
theorem six_unit_not_g2 :
    ∃ selected : RootSubset 6,
      (∀ alpha beta : PositiveRoot 6, RootOrder 6 (by decide) alpha beta →
        beta.val ∈ selected → alpha.val ∈ selected) ∧
      ¬ RootLattice.g2.Lower (RootLattice.g2Rescaling.image selected.carrier) := by
  let selected : RootSubset 6 := RootSubset.ofIndices {index | index.val ≤ 2}
  have hmem (index : Fin 6) : positiveRoot 6 index ∈ selected ↔ index.val ≤ 2 := by
    change index ∈ selected.indices ↔ _
    rw [RootSubset.indices_ofIndices]
    rfl
  refine ⟨selected, ?_, ?_⟩
  · intro alpha beta hle hbeta
    obtain ⟨first, rfl⟩ := (positiveRootEquiv 6).surjective alpha
    obtain ⟨second, rfl⟩ := (positiveRootEquiv 6).surjective beta
    rw [rootOrder_layers, PositiveRoot.index_equiv, PositiveRoot.index_equiv] at hle
    rw [positiveRootEquiv_val, hmem] at hbeta ⊢
    rcases hle with hequal | hlayer
    · have hindices := (positiveRootEquiv 6).injective hequal
      subst second
      exact hbeta
    · omega
  · intro hlower
    have halpha :
        PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3)
          (positiveRootEquiv 6 ⟨3, by decide⟩) • positiveRoot 6 ⟨3, by decide⟩ ∈
        RootLattice.g2Rescaling.image selected.carrier := by
      apply hlower.2 _ _
      · rw [RootLattice.g2Rescaling.carrier]
        exact ⟨positiveRootEquiv 6 ⟨3, by decide⟩, rfl⟩
      · rw [RootLattice.g2Rescaling.carrier]
        exact ⟨positiveRootEquiv 6 ⟨2, by decide⟩, rfl⟩
      · change RootLattice.g2.LE
          (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3)
            (positiveRootEquiv 6 ⟨3, by decide⟩) • positiveRoot 6 ⟨3, by decide⟩)
          (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3)
            (positiveRootEquiv 6 ⟨2, by decide⟩) • positiveRoot 6 ⟨2, by decide⟩)
        rw [g2_comparison]
        norm_num [gCoefficients]
      · apply (RootLattice.g2Rescaling.mem_image selected.carrier
          (positiveRootEquiv 6 ⟨2, by decide⟩)).mpr
        exact (hmem _).mpr (by decide)
    have := (RootLattice.g2Rescaling.mem_image selected.carrier
      (positiveRootEquiv 6 ⟨3, by decide⟩)).mp halpha
    change positiveRoot 6 ⟨3, by decide⟩ ∈ selected at this
    have hbad := (hmem _).mp this
    norm_num at hbad

private theorem g_lower_pred (first second : Fin 6)
    (hle : (gCoefficients first).1 ≤ (gCoefficients second).1 ∧
      (gCoefficients first).2 ≤ (gCoefficients second).2)
    (hsecond : second.val ≠ 2 ∧ second.val ≠ 5) : first.val ≠ 2 ∧ first.val ≠ 5 := by
  fin_cases first <;> fin_cases second <;> norm_num [gCoefficients] at *

/-- A G2 lower ideal can fail to be a lower subset of the corresponding unit directions. -/
theorem six_g2_not_unit :
    ∃ selected : RootSubset 6,
      RootLattice.g2.Lower (RootLattice.g2Rescaling.image selected.carrier) ∧
      ¬ (∀ alpha beta : PositiveRoot 6, RootOrder 6 (by decide) alpha beta →
        beta.val ∈ selected → alpha.val ∈ selected) := by
  let selected : RootSubset 6 := RootSubset.ofIndices {index | index.val ≠ 2 ∧ index.val ≠ 5}
  have hmem (index : Fin 6) :
      positiveRoot 6 index ∈ selected ↔ index.val ≠ 2 ∧ index.val ≠ 5 := by
    change index ∈ selected.indices ↔ _
    rw [RootSubset.indices_ofIndices]
    rfl
  refine ⟨selected, ⟨RootLattice.g2Rescaling.image_subset _, ?_⟩, ?_⟩
  · intro source target hsource htarget hle hselected
    rw [RootLattice.g2Rescaling.carrier] at hsource htarget
    obtain ⟨alpha, rfl⟩ := hsource
    obtain ⟨beta, rfl⟩ := htarget
    have hbeta := (RootLattice.g2Rescaling.mem_image selected.carrier beta).mp hselected
    apply (RootLattice.g2Rescaling.mem_image selected.carrier alpha).mpr
    obtain ⟨first, rfl⟩ := (positiveRootEquiv 6).surjective alpha
    obtain ⟨second, rfl⟩ := (positiveRootEquiv 6).surjective beta
    change RootLattice.g2.LE
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 first) •
        positiveRoot 6 first)
      (PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3) (positiveRootEquiv 6 second) •
        positiveRoot 6 second) at hle
    rw [g2_comparison] at hle
    change positiveRoot 6 second ∈ selected at hbeta
    change positiveRoot 6 first ∈ selected
    rw [hmem] at hbeta ⊢
    exact g_lower_pred _ _ hle hbeta
  · intro hlower
    have := hlower (positiveRootEquiv 6 ⟨2, by decide⟩)
      (positiveRootEquiv 6 ⟨4, by decide⟩) (by
        rw [rootOrder_layers, PositiveRoot.index_equiv, PositiveRoot.index_equiv]
        exact Or.inr (by decide)) ((hmem _).mpr (by decide))
    change positiveRoot 6 ⟨2, by decide⟩ ∈ selected at this
    have hbad := (hmem _).mp this
    norm_num at hbad

end Schubert.DihedralSplines

namespace Schubert.Dihedral.RootLattice

open Schubert.DihedralSplines

private def coefficients : Fin 3 → ℕ × ℕ := ![(1, 0), (0, 1), (1, 1)]

private theorem numbered_coefficients (index : Fin 3) : positiveRoot 3 index =
    ((coefficients index).1 : ℝ) • a2.first +
      ((coefficients index).2 : ℝ) • a2.second := by
  rw [a2_numbered]
  fin_cases index <;> norm_num [coefficients]

/-- Integer simple-root comparison and the real cone order agree on the A positive vectors. -/
theorem a2_order (alpha beta : PositiveRoot 3) :
    a2.LE alpha.val beta.val ↔ RootOrder 3 (by decide) alpha beta := by
  obtain ⟨first, rfl⟩ := (positiveRootEquiv 3).surjective alpha
  obtain ⟨second, rfl⟩ := (positiveRootEquiv 3).surjective beta
  rw [positiveRootEquiv_val, positiveRootEquiv_val, numbered_coefficients,
    numbered_coefficients, le_coefficients _ a2_independent]
  rw [Schubert.DihedralSplines.rootOrder_layers, PositiveRoot.index_equiv,
    PositiveRoot.index_equiv]
  have hequal : positiveRootEquiv 3 first = positiveRootEquiv 3 second ↔ first = second :=
    (positiveRootEquiv 3).injective.eq_iff
  rw [hequal]
  fin_cases first <;> fin_cases second <;> norm_num [coefficients]

/-- Arbitrary lower subsets agree for the integer and real cone orders in the A configuration. -/
theorem a2_lower_iff (selected : RootSubset 3) :
    a2.Lower selected.carrier ↔
      ∀ alpha beta : PositiveRoot 3, RootOrder 3 (by decide) alpha beta →
        beta.val ∈ selected → alpha.val ∈ selected := by
  constructor
  · intro hlower alpha beta hle hbeta
    exact hlower.2 _ _ (a2_positive.symm ▸ alpha.property)
      (a2_positive.symm ▸ beta.property) ((a2_order _ _).mpr hle) hbeta
  · intro hlower
    refine ⟨?_, ?_⟩
    · intro vector hvector
      rw [a2_positive]
      exact selected.positive hvector
    · intro alpha beta halpha hbeta hle hselected
      rw [a2_positive] at halpha hbeta
      exact hlower ⟨alpha, halpha⟩ ⟨beta, hbeta⟩ ((a2_order _ _).mp hle) hselected

end Schubert.Dihedral.RootLattice
