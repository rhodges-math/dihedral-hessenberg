import DihedralHessenberg.Paper.PentagonSteps
import DihedralHessenberg.Paper.FamilyBasis
import DihedralHessenberg.Paper.FamilyRank

/-! # The ten pentagon generators and their bases -/

noncomputable section
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral

/-- The displayed generator at each numbered vertex. -/
def generator (row : Fin 10) : HomogeneousAt ideal (vertices row) := by
  refine Fin.cases ?_ (fun row => ?_) row
  · exact FlowupSpline.identity ideal
  ·
    refine Fin.cases ?_ (fun row => ?_) row
    · exact rightLow
    ·
      refine Fin.cases ?_ (fun row => ?_) row
      · exact FlowupSpline.schubertAt ideal (vertices 2)
          (by rw [degrees, word_lengths]; decide)
      ·
        refine Fin.cases ?_ (fun row => ?_) row
        · exact leftLow
        ·
          refine Fin.cases ?_ (fun row => ?_) row
          · exact rightMiddle
          ·
            refine Fin.cases ?_ (fun row => ?_) row
            · exact afterBoth
            ·
              refine Fin.cases ?_ (fun row => ?_) row
              · exact leftMiddle
              ·
                refine Fin.cases ?_ (fun row => ?_) row
                · exact afterSecond
                ·
                  refine Fin.cases ?_ (fun row => ?_) row
                  · exact afterFirst
                  ·
                    refine Fin.cases ?_ (fun index => Fin.elim0 index) row
                    exact top

/-- The first two low generators are respectively the identity and the restricted Schubert spline.
-/
theorem initial_formulas :
    (generator 0).value = 1 ∧
    (generator 2).value = ideal.toRootSubset.restrictFull
      (SchubertSpline.spline 5 (by decide) (simpleRoot 5 (by decide) 0).reflection) := by
  constructor <;> rfl

/-- The other eight functions have exactly the displayed operator formulas. -/
theorem operator_formulas :
    (generator 1).value = ideal.toRootSubset.dot (by decide)
      ((simpleRoot 5 (by decide) 0).reflection * (simpleRoot 5 (by decide) 1).reflection)
        afterBoth.value ∧
    (generator 3).value = ideal.toRootSubset.dot (by decide)
      (simpleRoot 5 (by decide) 1).reflection afterBoth.value ∧
    (generator 4).value = ideal.toRootSubset.dot (by decide)
      ((simpleRoot 5 (by decide) 0).reflection * (simpleRoot 5 (by decide) 1).reflection)
        afterFirst.value ∧
    (generator 6).value = ideal.toRootSubset.dot (by decide)
      (simpleRoot 5 (by decide) 1).reflection afterFirst.value ∧
    (generator 5).value = ideal.dividedDifference afterSecond.value
      (simpleRoot 5 (by decide) 0) afterBoth_admissible ∧
    (generator 7).value = ideal.dividedDifference top.value
      (simpleRoot 5 (by decide) 1) afterSecond_admissible ∧
    (generator 8).value = ideal.dividedDifference top.value
      (simpleRoot 5 (by decide) 0) afterFirst_admissible ∧
    (generator 9).value = ideal.topSpline :=
  ⟨rightLow_word, leftLow_value, rightMiddle_word, leftMiddle_value,
    afterBoth_value, afterSecond_value, afterFirst_value, top_value⟩

/-- Each function has its prescribed root degree and upper support. -/
theorem certificates (row : Fin 10) :
    (generator row).value ∈ ideal.toRootSubset.piece
      ((![0, 1, 1, 1, 2, 1, 2, 2, 2, 3] : Fin 10 → ℕ) row) ∧
    (∀ current, ¬ BruhatLE 5 (by decide) (vertices row) current →
      ((generator row).value : DihedralGroup 5 → CoordinatePolynomial) current = 0) ∧
    ((generator row).value : DihedralGroup 5 → CoordinatePolynomial) (vertices row) ≠ 0 := by
  rw [← degrees]
  exact ⟨(generator row).homogeneous, (generator row).support, (generator row).diagonal⟩

/-- Each generator has exactly its displayed whole-spline degree. -/
theorem whole_degrees (row : Fin 10) :
    ideal.toRootSubset.degree (generator row).value =
      (![0, 1, 1, 1, 2, 1, 2, 2, 2, 3] : Fin 10 → ℕ) row := by
  rw [(generator row).degree_eq, degrees]

private theorem vertices_injective : Function.Injective vertices := by
  intro first second heq
  fin_cases first <;> fin_cases second
  all_goals norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two] at heq
  all_goals norm_num
  all_goals revert heq
  all_goals decide

private theorem vertices_surjective : Function.Surjective vertices := by
  intro element
  cases element with
  | r coordinate =>
    fin_cases coordinate <;>
      norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
    all_goals decide
  | sr coordinate =>
    fin_cases coordinate <;>
      norm_num [vertices, simpleRoot_reflection, simpleReflection, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
    all_goals decide

private def vertexEquiv : Fin 10 ≃ DihedralGroup 5 :=
  Equiv.ofBijective vertices ⟨vertices_injective, vertices_surjective⟩

private def certificate (vertex : DihedralGroup 5) : HomogeneousAt ideal vertex :=
  (vertexEquiv.apply_symm_apply vertex) ▸ generator (vertexEquiv.symm vertex)

/-- The functions form a triangular family on the group. -/
def family : TriangularFamily ideal := HomogeneousAt.family certificate

/-- The family retains each displayed generator. -/
theorem family_vertex (row : Fin 10) : family.value (vertices row) = (generator row).value := by
  have hcast {first second : DihedralGroup 5} (h : first = second)
      (value : HomogeneousAt ideal first) : (h ▸ value).value = value.value := by
    cases h
    rfl
  change (certificate (vertexEquiv row)).value = _
  have hvalue : (certificate (vertexEquiv row)).value =
      (generator (vertexEquiv.symm (vertexEquiv row))).value :=
    hcast _ _
  exact hvalue.trans (congrArg (fun index => (generator index).value)
    (vertexEquiv.symm_apply_apply row))

/-- Both named polynomial module structures have bases consisting of the generators. -/
theorem bases :
    (letI := ideal.toRootSubset.leftAlgebra (by decide)
      ∃ basis : Module.Basis (DihedralGroup 5) CoordinatePolynomial ideal.toRootSubset.Spline,
        ∀ row, basis (vertices row) = (generator row).value) ∧
    (letI := ideal.toRootSubset.rightAlgebra (by decide)
      ∃ basis : Module.Basis (DihedralGroup 5) CoordinatePolynomial ideal.toRootSubset.Spline,
        ∀ row, basis (vertices row) = (generator row).value) := by
  constructor
  · let := ideal.toRootSubset.leftAlgebra (by decide)
    refine ⟨TriangularFamily.Left.basis family, ?_⟩
    intro row
    rw [TriangularFamily.Left.basis_apply, family_vertex]
  · let := ideal.toRootSubset.rightAlgebra (by decide)
    refine ⟨TriangularFamily.Right.basis family, ?_⟩
    intro row
    rw [TriangularFamily.Right.basis_apply, family_vertex]

/-- The constant-scalar quotient rank polynomial is the stated pentagon polynomial. -/
theorem left_rank : HessenbergIdeal.Left.rankPolynomial ideal =
    1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * Polynomial.X^2 + Polynomial.X^3 := by
  rw [TriangularFamily.Left.rankPolynomial_eq family, polynomial]

/-- The orbit-scalar quotient rank polynomial is the same stated polynomial. -/
theorem right_rank : HessenbergIdeal.Right.rankPolynomial ideal =
    1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * Polynomial.X^2 + Polynomial.X^3 := by
  rw [TriangularFamily.Right.rankPolynomial_eq family, polynomial]

end Schubert.DihedralSplines.Pentagon
