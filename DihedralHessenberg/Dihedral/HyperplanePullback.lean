import DihedralHessenberg.Dihedral.RootChambers
import DihedralHessenberg.Dihedral.SimpleExtremal

/-! # Pulling back generic root hyperplanes through the linear action -/

noncomputable section

namespace Schubert.Dihedral.Separator

variable {n : ℕ} [NeZero n]

/-- The transpose-action normal for the inverse image of a generic hyperplane. -/
def transposeNormal (data : Separator n) (element : DihedralGroup n) : RealPlane :=
  ![realBilinearForm (realAction n element ![1, 0]) data.normal,
    realBilinearForm (realAction n element ![0, 1]) data.normal]

/-- Pairing with the transpose normal is exactly the pairing after the action. -/
theorem transpose_pairing (data : Separator n) (element : DihedralGroup n)
    (vector : RealPlane) :
    realBilinearForm vector (data.transposeNormal element) =
      realBilinearForm (realAction n element vector) data.normal := by
  have hexpand : vector = vector 0 • (![1, 0] : RealPlane) + vector 1 • ![0, 1] := by
    funext coordinate
    fin_cases coordinate <;> simp
  have hlinear : realAction n element vector =
      vector 0 • realAction n element ![1, 0] + vector 1 • realAction n element ![0, 1] := by
    change (realLinearEquiv n element) vector = _
    rw [hexpand, map_add, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add]
    rfl
  rw [hlinear]
  simp only [transposeNormal, realBilinearForm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The inverse-image hyperplane is still generic for the signed roots. -/
def pullback (data : Separator n) (element : DihedralGroup n) : Separator n where
  normal := data.transposeNormal element
  generic := fun vector hvector => by
    rw [data.transpose_pairing]
    exact data.generic _ (realAction_mem n element vector hvector)

/-- A chamber translate pulls its generic positive side back to the canonical positive roots. -/
theorem positive_pullback (data : Separator n) (element : DihedralGroup n)
    (himage : data.positive = realAction n element '' positiveRoots n) :
    (data.pullback element).positive = positiveRoots n := by
  ext vector
  constructor
  · intro hvector
    have hmem : realAction n element vector ∈ data.positive := by
      refine ⟨realAction_mem n element vector hvector.1, ?_⟩
      exact (data.transpose_pairing element vector) ▸ hvector.2
    rw [himage] at hmem
    obtain ⟨root, hroot, heq⟩ := hmem
    have hequal : root = vector := (realLinearEquiv n element).injective heq
    exact hequal ▸ hroot
  · intro hvector
    have hmem : realAction n element vector ∈ data.positive := by
      rw [himage]
      exact ⟨vector, hvector, rfl⟩
    refine ⟨Or.inl hvector, ?_⟩
    change 0 < realBilinearForm vector (data.transposeNormal element)
    rw [data.transpose_pairing]
    exact hmem.2

end Schubert.Dihedral.Separator
