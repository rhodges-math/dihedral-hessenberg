import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

/-! # Splitting total degree into monomial degree and basis weight -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- Total-degree pairs split uniquely into a monomial-degree fiber and a weight fiber. -/
def degreePairsEquiv {P I : Type*} (weight : I → ℕ) (degree : ℕ) :
    {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree} ≃
      Σ split : Fin (degree + 1),
        {exponent : P →₀ ℕ // exponent.degree = split.val} ×
          {index : I // weight index = degree - split.val} where
  toFun pair := ⟨⟨pair.val.1.degree, by have := pair.property; omega⟩,
    ⟨pair.val.1, rfl⟩, ⟨pair.val.2, by
      change weight pair.val.2 = degree - pair.val.1.degree
      have := pair.property
      omega⟩⟩
  invFun split := ⟨(split.2.1.val, split.2.2.val), by
    change split.2.1.val.degree + weight split.2.2.val = degree
    have hdegree := split.1.isLt
    have hexponent := split.2.1.property
    have hweight := split.2.2.property
    omega⟩
  left_inv pair := Subtype.ext rfl
  right_inv split := by
    rcases split with ⟨⟨split, hsplit⟩, ⟨exponent, hexponent⟩, ⟨index, hindex⟩⟩
    cases hexponent
    rfl

/-- The split degree is the monomial degree. -/
@[simp] theorem degreePairsEquiv_degree {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (pair : {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree}) :
    ((degreePairsEquiv weight degree) pair).1.val = pair.val.1.degree := rfl

/-- Degree splitting preserves the monomial exponent. -/
@[simp] theorem degreePairsEquiv_exponent {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (pair : {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree}) :
    ((degreePairsEquiv weight degree) pair).2.1.val = pair.val.1 := rfl

/-- Degree splitting preserves the basis index. -/
@[simp] theorem degreePairsEquiv_index {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (pair : {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree}) :
    ((degreePairsEquiv weight degree) pair).2.2.val = pair.val.2 := rfl

/-- Joining degree fibers returns exactly the exponent-index pair. -/
@[simp] theorem degreePairsEquiv_symm_val {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (split : Σ split : Fin (degree + 1),
      {exponent : P →₀ ℕ // exponent.degree = split.val} ×
        {index : I // weight index = degree - split.val}) :
    ((degreePairsEquiv weight degree).symm split).val = (split.2.1.val, split.2.2.val) := rfl

end Schubert.FiniteGroupCharacters
