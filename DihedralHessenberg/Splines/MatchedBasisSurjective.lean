import DihedralHessenberg.Splines.GradedEmbeddingSurjective
import DihedralHessenberg.Splines.ArbitraryHomogeneousBasis
import DihedralHessenberg.FiniteGroupCharacters.EmbeddedHomogeneousBasis

/-! An injective map with matched homogeneous basis degree fibers is surjective. -/

noncomputable section
namespace Schubert.Splines

/-- An injective map with matched homogeneous basis degree fibers is surjective. -/
theorem surjective_of_matched_bases {K M N I J : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (pieces : ℕ → Submodule K N) [DirectSum.Decomposition pieces]
    (hinternal : DirectSum.IsInternal pieces) (hfinite : ∀ degree, Module.Finite K (pieces degree))
    (embedding : M →ₗ[K] N) (hinjective : Function.Injective embedding)
    (sourceBasis : Module.Basis I K M) (targetBasis : Module.Basis J K N)
    (sourceDegrees : I → ℕ) (targetDegrees : J → ℕ)
    (hsource : ∀ index, embedding (sourceBasis index) ∈ pieces (sourceDegrees index))
    (htarget : ∀ index, targetBasis index ∈ pieces (targetDegrees index))
    (indices : I ≃ J) (hdegrees : ∀ index, targetDegrees (indices index) = sourceDegrees index) :
    Function.Surjective embedding := by
  have hfibers (degree : ℕ) :
      {index // sourceDegrees index = degree} ≃ {index // targetDegrees index = degree} :=
    indices.subtypeEquiv (fun index => by rw [hdegrees])
  apply surjective_of_piece_finrank pieces hinternal embedding hinjective
  · intro degree
    let := hfinite degree
    let restricted := arbitraryHomogeneousPieceBasis pieces targetBasis targetDegrees htarget degree
    let : Finite {index // targetDegrees index = degree} := restricted.linearIndependent.finite
    let : Finite {index // sourceDegrees index = degree} := Finite.of_equiv _ (hfibers degree).symm
    exact Schubert.FiniteGroupCharacters.embedded_homogeneousPiece_finite pieces embedding
      hinjective sourceBasis sourceDegrees hsource degree
  · exact hfinite
  · intro degree
    rw [Schubert.FiniteGroupCharacters.embedded_homogeneousPiece_finrank pieces embedding
      hinjective sourceBasis sourceDegrees hsource degree,
      arbitraryHomogeneousPieceBasis_finrank pieces targetBasis targetDegrees htarget degree]
    exact Nat.card_congr (hfibers degree)

end Schubert.Splines
