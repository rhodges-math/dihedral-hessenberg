import Schubert.DihedralSplines.FamilyBasis

/-! # Arbitrary flow-up bases and triangular families -/

noncomputable section

namespace Schubert.DihedralSplines.TriangularFamily

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- A flow-up spline is a vector of some qualifying triangular family. -/
def IsMember (value : ideal.toRootSubset.Spline) : Prop :=
  ∃ family : TriangularFamily ideal, ∃ vertex, family.value vertex = value

/-- A flow-up spline at a vertex has that vertex as its minimal support element. -/
def At (value : ideal.toRootSubset.Spline) (vertex : DihedralGroup n) : Prop :=
  IsMember ideal value ∧
    (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 ∧
    ∀ current, (value : DihedralGroup n → CoordinatePolynomial) current ≠ 0 →
      BruhatLE n hthree current vertex → current = vertex

/-- Each triangular vector is a flow-up spline at its indexing vertex. -/
theorem family_at (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    At ideal (family.value vertex) vertex := by
  refine ⟨⟨family, vertex, rfl⟩, family.diagonal vertex, ?_⟩
  intro current hnonzero hle
  have hupper : BruhatLE n hthree vertex current := by
    by_contra hnot
    exact hnonzero (family.support vertex current hnot)
  exact bruhatLE_antisymm n hthree hle hupper

/-- The minimal support element of a flow-up spline is also its least support element. -/
theorem at_least (value : ideal.toRootSubset.Spline) (vertex : DihedralGroup n)
    (hat : At ideal value vertex) (current : DihedralGroup n)
    (hcurrent : (value : DihedralGroup n → CoordinatePolynomial) current ≠ 0) :
    BruhatLE n hthree vertex current := by
  obtain ⟨family, base, hvalue⟩ := hat.1
  subst value
  have hbase : BruhatLE n hthree base vertex := by
    by_contra hnot
    exact hat.2.1 (family.support base vertex hnot)
  have heq : base = vertex := hat.2.2 base (family.diagonal base) hbase
  rw [← heq]
  by_contra hnot
  exact hcurrent (family.support base current hnot)

namespace Left

/-- An arbitrary polynomial basis satisfying the whole-degree triangular conditions. -/
def IsFlowup :
    (letI := ideal.toRootSubset.leftAlgebra hthree;
      Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline) → Prop := by
  letI := ideal.toRootSubset.leftAlgebra hthree
  exact fun vectors =>
    (∀ first second, ¬BruhatLE n hthree first second →
      (vectors first : DihedralGroup n → CoordinatePolynomial) second = 0) ∧
    (∀ vertex, (vectors vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) ∧
    (∀ vertex, ideal.toRootSubset.degree (vectors vertex) = ideal.toRootSubset.length vertex)

/-- Exactly the bases of arbitrary triangular families are flow-up bases. -/
theorem isFlowup_iff
    (vectors : letI := ideal.toRootSubset.leftAlgebra hthree;
      Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline) :
    IsFlowup ideal vectors ↔ ∃ family : TriangularFamily ideal, basis family = vectors := by
  let := ideal.toRootSubset.leftAlgebra hthree
  constructor
  · rintro ⟨hsupport, hdiagonal, hdegree⟩
    let family : TriangularFamily ideal :=
      ⟨vectors, hsupport, hdiagonal, hdegree⟩
    refine ⟨family, ?_⟩
    apply DFunLike.ext
    intro vertex
    exact basis_apply family vertex
  · rintro ⟨family, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro first second hnot
      rw [basis_apply]
      exact family.support first second hnot
    · intro vertex
      rw [basis_apply]
      exact family.diagonal vertex
    · intro vertex
      rw [basis_apply]
      exact family.degree_eq vertex

/-- Membership means membership in some arbitrary constant-scalar flow-up basis. -/
theorem member_iff (value : ideal.toRootSubset.Spline) :
    IsMember ideal value ↔
      (letI := ideal.toRootSubset.leftAlgebra hthree;
        ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline,
          IsFlowup ideal vectors ∧ ∃ vertex, vectors vertex = value) := by
  let := ideal.toRootSubset.leftAlgebra hthree
  constructor
  · rintro ⟨family, vertex, hvalue⟩
    exact ⟨basis family, (isFlowup_iff ideal _).mpr ⟨family, rfl⟩,
      vertex, (basis_apply family vertex).trans hvalue⟩
  · rintro ⟨vectors, hflowup, vertex, hvalue⟩
    obtain ⟨family, heq⟩ := (isFlowup_iff ideal vectors).mp hflowup
    refine ⟨family, vertex, ?_⟩
    rw [← basis_apply family vertex, heq]
    exact hvalue

end Left

namespace Right

/-- An arbitrary polynomial basis satisfying the whole-degree triangular conditions. -/
def IsFlowup :
    (letI := ideal.toRootSubset.rightAlgebra hthree;
      Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline) → Prop := by
  letI := ideal.toRootSubset.rightAlgebra hthree
  exact fun vectors =>
    (∀ first second, ¬BruhatLE n hthree first second →
      (vectors first : DihedralGroup n → CoordinatePolynomial) second = 0) ∧
    (∀ vertex, (vectors vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) ∧
    (∀ vertex, ideal.toRootSubset.degree (vectors vertex) = ideal.toRootSubset.length vertex)

/-- Exactly the bases of arbitrary triangular families are flow-up bases. -/
theorem isFlowup_iff
    (vectors : letI := ideal.toRootSubset.rightAlgebra hthree;
      Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline) :
    IsFlowup ideal vectors ↔ ∃ family : TriangularFamily ideal, basis family = vectors := by
  let := ideal.toRootSubset.rightAlgebra hthree
  constructor
  · rintro ⟨hsupport, hdiagonal, hdegree⟩
    let family : TriangularFamily ideal :=
      ⟨vectors, hsupport, hdiagonal, hdegree⟩
    refine ⟨family, ?_⟩
    apply DFunLike.ext
    intro vertex
    exact basis_apply family vertex
  · rintro ⟨family, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro first second hnot
      rw [basis_apply]
      exact family.support first second hnot
    · intro vertex
      rw [basis_apply]
      exact family.diagonal vertex
    · intro vertex
      rw [basis_apply]
      exact family.degree_eq vertex

/-- Membership means membership in some arbitrary orbit-scalar flow-up basis. -/
theorem member_iff (value : ideal.toRootSubset.Spline) :
    IsMember ideal value ↔
      (letI := ideal.toRootSubset.rightAlgebra hthree;
        ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline,
          IsFlowup ideal vectors ∧ ∃ vertex, vectors vertex = value) := by
  let := ideal.toRootSubset.rightAlgebra hthree
  constructor
  · rintro ⟨family, vertex, hvalue⟩
    exact ⟨basis family, (isFlowup_iff ideal _).mpr ⟨family, rfl⟩,
      vertex, (basis_apply family vertex).trans hvalue⟩
  · rintro ⟨vectors, hflowup, vertex, hvalue⟩
    obtain ⟨family, heq⟩ := (isFlowup_iff ideal vectors).mp hflowup
    refine ⟨family, vertex, ?_⟩
    rw [← basis_apply family vertex, heq]
    exact hvalue

end Right

end Schubert.DihedralSplines.TriangularFamily
