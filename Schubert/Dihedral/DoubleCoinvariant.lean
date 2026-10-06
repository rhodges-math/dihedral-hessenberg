import Schubert.Dihedral.InvariantGeneration
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # The double polynomial quotient by equal basic invariants -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral.DoubleCoinvariant

/-- Polynomials in the two pairs of coordinate variables. -/
abbrev DoublePolynomial := MvPolynomial (Fin 2 ⊕ Fin 2) ℂ

/-- The ideal equating the two copies of each basic invariant. -/
def relations (n : ℕ) : Ideal DoublePolynomial :=
  Ideal.span {MvPolynomial.rename Sum.inl quadraticInvariant -
    MvPolynomial.rename Sum.inr quadraticInvariant,
    MvPolynomial.rename Sum.inl (higherInvariant n) -
      MvPolynomial.rename Sum.inr (higherInvariant n)}

/-- The double coinvariant presentation. -/
abbrev Presentation (n : ℕ) := DoublePolynomial ⧸ relations n

/-- The first coordinate-polynomial copy in the double presentation. -/
def firstMap (n : ℕ) : CoordinatePolynomial →ₐ[ℂ] Presentation n :=
  (Ideal.Quotient.mkₐ ℂ (relations n)).comp (MvPolynomial.rename Sum.inl)

/-- The second coordinate-polynomial copy in the double presentation. -/
def secondMap (n : ℕ) : CoordinatePolynomial →ₐ[ℂ] Presentation n :=
  (Ideal.Quotient.mkₐ ℂ (relations n)).comp (MvPolynomial.rename Sum.inr)

/-- The two basic invariant images agree in the double presentation. -/
theorem basic_equal (n : ℕ) :
    firstMap n quadraticInvariant = secondMap n quadraticInvariant ∧
      firstMap n (higherInvariant n) = secondMap n (higherInvariant n) := by
  constructor
  · change Ideal.Quotient.mk (relations n) _ = Ideal.Quotient.mk (relations n) _
    apply Ideal.Quotient.eq.mpr
    exact Ideal.subset_span (by simp)
  · change Ideal.Quotient.mk (relations n) _ = Ideal.Quotient.mk (relations n) _
    apply Ideal.Quotient.eq.mpr
    exact Ideal.subset_span (by simp)

/-- The two maps agree on every invariant, not just the basic generators. -/
theorem invariant_equal (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (invariant : invariantSubalgebra n) :
    firstMap n invariant.val = secondMap n invariant.val := by
  have hle : invariantSubalgebra n ≤ AlgHom.equalizer (firstMap n) (secondMap n) := by
    rw [Invariants.eq_generator_adjoin n hthree]
    apply AlgHom.adjoin_le_equalizer
    intro polynomial hpolynomial
    rcases hpolynomial with rfl | hpolynomial
    · exact (basic_equal n).1
    · obtain rfl := hpolynomial
      exact (basic_equal n).2
  exact hle invariant.property

/-- The two basic relations generate exactly all invariant differences. -/
theorem relations_invariants (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    relations n = Ideal.span (Set.range fun invariant : invariantSubalgebra n =>
      MvPolynomial.rename Sum.inl invariant.val -
        MvPolynomial.rename Sum.inr invariant.val) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro polynomial hpolynomial
    rcases hpolynomial with rfl | hpolynomial
    · exact Ideal.subset_span ⟨⟨quadraticInvariant, Invariants.F2.mem n⟩, rfl⟩
    · obtain rfl := hpolynomial
      exact Ideal.subset_span
        ⟨⟨higherInvariant n, higherInvariant_mem_invariantSubalgebra n⟩, rfl⟩
  · apply Ideal.span_le.mpr
    rintro polynomial ⟨invariant, rfl⟩
    exact Ideal.Quotient.eq.mp (invariant_equal n hthree invariant)

/-- The first polynomial copy supplies the polynomial scalar structure. -/
local instance firstAlgebra (n : ℕ) : Algebra CoordinatePolynomial (Presentation n) :=
  (firstMap n).toRingHom.toAlgebra

local instance firstTower (n : ℕ) : IsScalarTower ℂ CoordinatePolynomial (Presentation n) :=
  IsScalarTower.of_algebraMap_eq fun scalar => ((firstMap n).commutes scalar).symm

/-- Invariant scalars act through their first polynomial copy. -/
local instance invariantAlgebra (n : ℕ) [NeZero n] :
    Algebra (invariantSubalgebra n) (Presentation n) :=
  ((firstMap n).toRingHom.comp (invariantSubalgebra n).val.toRingHom).toAlgebra

local instance invariantTower (n : ℕ) [NeZero n] :
    IsScalarTower (invariantSubalgebra n) CoordinatePolynomial (Presentation n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The second polynomial copy is linear over the invariant subalgebra. -/
def secondInvariantMap (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    CoordinatePolynomial →ₐ[invariantSubalgebra n] Presentation n where
  __ := (secondMap n).toRingHom
  commutes' invariant := (invariant_equal n hthree invariant).symm

/-- The balanced tensor evaluates into the double polynomial presentation. -/
def tensorMap (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial →ₐ[CoordinatePolynomial]
      Presentation n := by
  exact @AlgHom.liftEquiv (invariantSubalgebra n) CoordinatePolynomial CoordinatePolynomial
    (Presentation n) _ _ _ _ _ (firstAlgebra n) _ (invariantAlgebra n)
    (invariantTower n) (secondInvariantMap n hthree)

/-- A pure tensor retains its two polynomial copies. -/
theorem tensorMap_tmul (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (first second : CoordinatePolynomial) :
    tensorMap n hthree (first ⊗ₜ[invariantSubalgebra n] second) =
      firstMap n first * secondMap n second := rfl

/-- The double polynomial algebra evaluates in its two balanced tensor factors. -/
def polynomialMap (n : ℕ) [NeZero n] :
    DoublePolynomial →ₐ[ℂ]
      CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial :=
  MvPolynomial.aeval (Sum.elim
    (fun index => MvPolynomial.X index ⊗ₜ[invariantSubalgebra n] 1)
    (fun index => 1 ⊗ₜ[invariantSubalgebra n] MvPolynomial.X index))

/-- First-copy substitution gives the first tensor factor. -/
theorem polynomialMap_first (n : ℕ) [NeZero n] (polynomial : CoordinatePolynomial) :
    polynomialMap n (MvPolynomial.rename Sum.inl polynomial) =
      polynomial ⊗ₜ[invariantSubalgebra n] 1 := by
  have hmaps : (polynomialMap n).comp (MvPolynomial.rename Sum.inl) =
      (Algebra.TensorProduct.includeLeft : CoordinatePolynomial →ₐ[CoordinatePolynomial]
        CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial).restrictScalars ℂ := by
    ext index
    simp [polynomialMap]
  exact AlgHom.congr_fun hmaps polynomial

/-- Second-copy substitution gives the second tensor factor. -/
theorem polynomialMap_second (n : ℕ) [NeZero n] (polynomial : CoordinatePolynomial) :
    polynomialMap n (MvPolynomial.rename Sum.inr polynomial) =
      1 ⊗ₜ[invariantSubalgebra n] polynomial := by
  have hmaps : (polynomialMap n).comp (MvPolynomial.rename Sum.inr) =
      (Algebra.TensorProduct.includeRight : CoordinatePolynomial →ₐ[invariantSubalgebra n]
        CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial).restrictScalars ℂ := by
    ext index
    simp [polynomialMap]
  exact AlgHom.congr_fun hmaps polynomial

/-- Every invariant can be moved between the balanced tensor factors. -/
theorem invariant_tmul (n : ℕ) [NeZero n] (invariant : invariantSubalgebra n) :
    invariant.val ⊗ₜ[invariantSubalgebra n] (1 : CoordinatePolynomial) =
      (1 : CoordinatePolynomial) ⊗ₜ[invariantSubalgebra n] invariant.val := by
  exact RingHom.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := invariantSubalgebra n) (A := CoordinatePolynomial) (B := CoordinatePolynomial))
    invariant

/-- The two defining invariant differences vanish in the balanced tensor. -/
theorem relations_kernel (n : ℕ) [NeZero n] :
    relations n ≤ RingHom.ker (polynomialMap n).toRingHom := by
  apply Ideal.span_le.mpr
  intro polynomial hpolynomial
  rcases hpolynomial with rfl | hpolynomial
  · change polynomialMap n (_ - _) = 0
    rw [map_sub, polynomialMap_first, polynomialMap_second, sub_eq_zero]
    exact invariant_tmul n ⟨quadraticInvariant, Invariants.F2.mem n⟩
  · obtain rfl := hpolynomial
    change polynomialMap n (_ - _) = 0
    rw [map_sub, polynomialMap_first, polynomialMap_second, sub_eq_zero]
    exact invariant_tmul n ⟨higherInvariant n, higherInvariant_mem_invariantSubalgebra n⟩

/-- The double polynomial quotient maps to the balanced tensor. -/
def presentationMap (n : ℕ) [NeZero n] :
    Presentation n →ₐ[ℂ]
      CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial :=
  Ideal.Quotient.liftₐ (relations n) (polynomialMap n)
    (fun _ hmem => relations_kernel n hmem)

/-- A first-copy polynomial maps to its first tensor factor. -/
theorem presentationMap_first (n : ℕ) [NeZero n] (polynomial : CoordinatePolynomial) :
    presentationMap n (firstMap n polynomial) =
      polynomial ⊗ₜ[invariantSubalgebra n] 1 := polynomialMap_first n polynomial

/-- A second-copy polynomial maps to its second tensor factor. -/
theorem presentationMap_second (n : ℕ) [NeZero n] (polynomial : CoordinatePolynomial) :
    presentationMap n (secondMap n polynomial) =
      1 ⊗ₜ[invariantSubalgebra n] polynomial := polynomialMap_second n polynomial

/-- Mapping a balanced tensor through the presentation and back preserves it. -/
theorem presentation_tensor (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    (presentationMap n).comp ((tensorMap n hthree).restrictScalars ℂ) =
      AlgHom.id ℂ (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) := by
  apply AlgHom.ext
  intro value
  induction value using TensorProduct.inductionOn with
  | tmul first second =>
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.id_apply,
        tensorMap_tmul, map_mul, presentationMap_first, presentationMap_second,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add first second hfirst hsecond =>
      simp only [map_add, hfirst, hsecond]

/-- Mapping a double polynomial class through the balanced tensor and back preserves it. -/
theorem tensor_presentation (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ((tensorMap n hthree).restrictScalars ℂ).comp (presentationMap n) =
      AlgHom.id ℂ (Presentation n) := by
  have hpoly : (((tensorMap n hthree).restrictScalars ℂ).comp (presentationMap n)).comp
      (Ideal.Quotient.mkₐ ℂ (relations n)) = Ideal.Quotient.mkₐ ℂ (relations n) := by
    ext coordinate
    cases coordinate with
    | inl index =>
        change tensorMap n hthree
          (polynomialMap n (MvPolynomial.X (Sum.inl index))) = _
        rw [show polynomialMap n (MvPolynomial.X (Sum.inl index)) =
          MvPolynomial.X index ⊗ₜ[invariantSubalgebra n] 1 from MvPolynomial.aeval_X _ _]
        rw [tensorMap_tmul, map_one, mul_one]
        simp [firstMap]
    | inr index =>
        change tensorMap n hthree
          (polynomialMap n (MvPolynomial.X (Sum.inr index))) = _
        rw [show polynomialMap n (MvPolynomial.X (Sum.inr index)) =
          1 ⊗ₜ[invariantSubalgebra n] MvPolynomial.X index from MvPolynomial.aeval_X _ _]
        rw [tensorMap_tmul, map_one, one_mul]
        simp [secondMap]
  apply AlgHom.ext
  intro value
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
  exact AlgHom.congr_fun hpoly polynomial

/-- The double polynomial presentation is the tensor over invariants. -/
def tensorEquiv (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Presentation n ≃ₐ[ℂ]
      CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial :=
  AlgEquiv.ofAlgHom (presentationMap n) ((tensorMap n hthree).restrictScalars ℂ)
    (presentation_tensor n hthree) (tensor_presentation n hthree)

/-- The tensor equivalence sends a first-copy polynomial to the first factor. -/
theorem tensorEquiv_first (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) :
    tensorEquiv n hthree (firstMap n polynomial) =
      polynomial ⊗ₜ[invariantSubalgebra n] 1 := presentationMap_first n polynomial

/-- The tensor equivalence sends a second-copy polynomial to the second factor. -/
theorem tensorEquiv_second (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) :
    tensorEquiv n hthree (secondMap n polynomial) =
      1 ⊗ₜ[invariantSubalgebra n] polynomial := presentationMap_second n polynomial

/-- The double presentation equivalence respects its first polynomial scalars. -/
def scalarEquiv (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Presentation n ≃ₐ[CoordinatePolynomial]
      CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial where
  __ := (tensorEquiv n hthree).toRingEquiv
  commutes' polynomial := tensorEquiv_first n hthree polynomial

end Schubert.Dihedral.DoubleCoinvariant
