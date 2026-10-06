import Schubert.Dihedral.CosetDecomposition
import Schubert.Dihedral.SignTwist
import Schubert.Dihedral.SimpleScalar

/-! # Determinant twists of simple-root coset complements -/

noncomputable section
namespace Schubert.Dihedral
variable {n : ℕ} [NeZero n]

/-- Sign multiplication exchanges the two simple-root coset complements. -/
theorem sign_coset_complement (hthree : 3 ≤ n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) (endpoint : ℕ) :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      (TauCeti.SplitK0.of alpha.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n endpoint)) =
      TauCeti.SplitK0.of beta.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n endpoint) :=
  by
  by_cases heven : Even n
  · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [PositiveRoot.coset_even_class _ heven, PositiveRoot.coset_even_class _ heven,
        first_simple_scalar n hthree heven, second_simple_scalar n hthree heven,
        mul_sub, mul_add, sign_even_class, sign_partialSum_class, sign_partialSum_class]
      simp only [Bool.not_false]
      abel
    · rw [PositiveRoot.coset_even_class _ heven, PositiveRoot.coset_even_class _ heven,
        second_simple_scalar n hthree heven, first_simple_scalar n hthree heven,
        mul_sub, mul_add, sign_even_class, sign_partialSum_class, sign_partialSum_class]
      simp only [Bool.not_true]
      abel
  · rw [PositiveRoot.coset_odd_class _ (Nat.not_even_iff_odd.mp heven),
      PositiveRoot.coset_odd_class _ (Nat.not_even_iff_odd.mp heven),
      mul_sub, sign_partialSum_class, sign_partialSum_class]
    abel

end Schubert.Dihedral
