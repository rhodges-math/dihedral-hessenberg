import DihedralHessenberg.Dihedral.RootInversionSets
import DihedralHessenberg.Dihedral.RootObjectAction

/-! # Reflection descent criteria for geometric root inversion sets -/

namespace Schubert.Dihedral

namespace PositiveRoot

/-- A positive vector is a right inversion exactly when its reflection decreases length. -/
theorem right_descent {n : ℕ} (hthree : 3 ≤ n) (element : DihedralGroup n)
    (alpha : PositiveRoot n) :
    alpha.val ∈ rightInversionSet n element ↔
      length n hthree (element * alpha.reflection) < length n hthree element := by
  rw [← alpha.index_val, mem_rightInversionSet, mem_rightInversions]
  rfl

/-- A positive vector is a left inversion exactly when its reflection decreases length. -/
theorem left_descent {n : ℕ} (hthree : 3 ≤ n) (element : DihedralGroup n)
    (alpha : PositiveRoot n) :
    alpha.val ∈ leftInversionSet n element ↔
      length n hthree (alpha.reflection * element) < length n hthree element := by
  rw [← alpha.index_val, mem_leftInversionSet, mem_leftInversions]
  rfl

/-- Equality of complex root images determines the real image. -/
theorem image_eq {n : ℕ} (element : DihedralGroup n) (alpha beta : PositiveRoot n)
    (himage : vectorOperator n element (complexify alpha.val) = complexify beta.val) :
    realAction n element alpha.val = beta.val := by
  funext coordinate
  have hcoordinate := congrArg Complex.re (congrFun himage coordinate)
  simpa only [realAction, complexify, Complex.ofReal_re] using hcoordinate

end PositiveRoot

/-- The geometric right inversion set is exactly the set defined by reflection descent. -/
theorem rightInversionSet_descent (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    rightInversionSet n element = Subtype.val ''
      {alpha : PositiveRoot n |
        length n hthree (element * alpha.reflection) < length n hthree element} := by
  ext vector
  constructor
  · intro hmem
    exact ⟨⟨vector, hmem.1⟩, (PositiveRoot.right_descent hthree element _).mp hmem, rfl⟩
  · rintro ⟨alpha, halpha, rfl⟩
    exact (PositiveRoot.right_descent hthree element alpha).mpr halpha

/-- The geometric left inversion set is exactly the set defined by reflection descent. -/
theorem leftInversionSet_descent (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    leftInversionSet n element = Subtype.val ''
      {alpha : PositiveRoot n |
        length n hthree (alpha.reflection * element) < length n hthree element} := by
  ext vector
  constructor
  · intro hmem
    exact ⟨⟨vector, hmem.1⟩, (PositiveRoot.left_descent hthree element _).mp hmem, rfl⟩
  · rintro ⟨alpha, halpha, rfl⟩
    exact (PositiveRoot.left_descent hthree element alpha).mpr halpha

end Schubert.Dihedral
