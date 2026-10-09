import DihedralHessenberg.FiniteGroupCharacters.DegreePairs

/-! # Splitting total degree with a positive monomial factor -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- Positive monomial-degree pairs split into a positive degree and a weight fiber. -/
def positiveDegreePairsEquiv {P I : Type*} (weight : I → ℕ) (degree : ℕ) :
    {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree ∧ pair.1 ≠ 0} ≃
      Σ split : Fin degree,
        {exponent : P →₀ ℕ // exponent.degree = split.val + 1} ×
          {index : I // weight index = degree - (split.val + 1)} where
  toFun pair := ⟨⟨pair.val.1.degree - 1, by
    have hpositive : pair.val.1.degree ≠ 0 := by
      exact (Finsupp.degree_eq_zero_iff pair.val.1).not.mpr pair.property.2
    have := pair.property.1
    omega⟩, ⟨pair.val.1, by
      change pair.val.1.degree = pair.val.1.degree - 1 + 1
      have hpositive : pair.val.1.degree ≠ 0 := by
        exact (Finsupp.degree_eq_zero_iff pair.val.1).not.mpr pair.property.2
      omega⟩, ⟨pair.val.2, by
      change weight pair.val.2 = degree - (pair.val.1.degree - 1 + 1)
      have hpositive : pair.val.1.degree ≠ 0 := by
        exact (Finsupp.degree_eq_zero_iff pair.val.1).not.mpr pair.property.2
      have := pair.property.1
      omega⟩⟩
  invFun split := ⟨(split.2.1.val, split.2.2.val), by
    constructor
    · have hdegree := split.1.isLt
      have hexponent := split.2.1.property
      have hweight := split.2.2.property
      change split.2.1.val.degree + weight split.2.2.val = degree
      omega
    · intro hzero
      change split.2.1.val = 0 at hzero
      have hexponent := split.2.1.property
      have hdegzero : split.2.1.val.degree = 0 :=
        (Finsupp.degree_eq_zero_iff _).mpr hzero
      omega⟩
  left_inv pair := Subtype.ext rfl
  right_inv split := by
    rcases split with ⟨⟨split, hsplit⟩, ⟨exponent, hexponent⟩, ⟨index, hindex⟩⟩
    change exponent.degree = split + 1 at hexponent
    have hsplit : exponent.degree - 1 = split := by omega
    subst split
    rfl

/-- The positive split coordinate is the monomial degree minus one. -/
@[simp] theorem positiveDegreePairsEquiv_degree {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (pair : {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree ∧ pair.1 ≠ 0}) :
    ((positiveDegreePairsEquiv weight degree) pair).1.val = pair.val.1.degree - 1 := rfl

/-- Positive degree splitting preserves the monomial exponent. -/
@[simp] theorem positiveDegreePairsEquiv_exponent {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (pair : {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree ∧ pair.1 ≠ 0}) :
    ((positiveDegreePairsEquiv weight degree) pair).2.1.val = pair.val.1 := rfl

/-- Positive degree splitting preserves the basis index. -/
@[simp] theorem positiveDegreePairsEquiv_index {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (pair : {pair : (P →₀ ℕ) × I // pair.1.degree + weight pair.2 = degree ∧ pair.1 ≠ 0}) :
    ((positiveDegreePairsEquiv weight degree) pair).2.2.val = pair.val.2 := rfl

/-- Joining positive degree fibers returns the exponent-index pair. -/
@[simp] theorem positiveDegreePairsEquiv_symm_val {P I : Type*} (weight : I → ℕ) (degree : ℕ)
    (split : Σ split : Fin degree,
      {exponent : P →₀ ℕ // exponent.degree = split.val + 1} ×
        {index : I // weight index = degree - (split.val + 1)}) :
    ((positiveDegreePairsEquiv weight degree).symm split).val =
      (split.2.1.val, split.2.2.val) := rfl

end Schubert.FiniteGroupCharacters
