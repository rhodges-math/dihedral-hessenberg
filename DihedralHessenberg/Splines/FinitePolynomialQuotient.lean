import DihedralHessenberg.Splines.QuotientFinite

/-! # Finite polynomial-module quotients without a basis hypothesis -/

namespace Schubert.Splines

variable {K P A B : Type*} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]
variable [Algebra (MvPolynomial P K) A] [IsScalarTower K (MvPolynomial P K) A]

/-- Killing coordinates in a quotient of a finite polynomial module gives coefficient finiteness. -/
theorem _root_.Schubert.Splines.QuotientFinite.finite_of_X_zero
    [Module.Finite (MvPolynomial P K) A] (quotient : A →ₐ[K] B)
    (hsurjective : Function.Surjective quotient)
    (hzero : ∀ coordinate,
      quotient (algebraMap (MvPolynomial P K) A (MvPolynomial.X coordinate)) = 0) :
    Module.Finite K B := by
  classical
  obtain ⟨generators, hgenerators⟩ :=
    (Module.Finite.fg_top (R := MvPolynomial P K) (M := A))
  have hspan : Submodule.span K (quotient '' (generators : Set A)) = ⊤ := by
    apply top_unique
    intro value _
    obtain ⟨representative, rfl⟩ := hsurjective value
    have hmember : representative ∈ Submodule.span (MvPolynomial P K) (generators : Set A) := by
      rw [hgenerators]
      exact Submodule.mem_top
    induction hmember using Submodule.span_induction with
    | mem member hmember => exact Submodule.subset_span ⟨member, hmember, rfl⟩
    | zero => exact map_zero quotient ▸ Submodule.zero_mem _
    | add first second _ _ hfirst hsecond =>
      simpa only [map_add] using
        Submodule.add_mem _ (hfirst Submodule.mem_top) (hsecond Submodule.mem_top)
    | smul scalar member _ hmember =>
      rw [Algebra.smul_def, map_mul]
      have hscalar := _root_.Schubert.Splines.QuotientFinite.apply_eq_constantCoeff
        (quotient.comp (IsScalarTower.toAlgHom K (MvPolynomial P K) A)) hzero scalar
      change quotient (algebraMap (MvPolynomial P K) A scalar) = _ at hscalar
      rw [hscalar, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hmember Submodule.mem_top)
  constructor
  rw [← hspan]
  exact Submodule.fg_span ((generators.finite_toSet).image quotient)

end Schubert.Splines
