import Schubert.DihedralSplines.PaperQuotientGrading
import Schubert.Splines.QuotientRepresentation

/-! # Dot representations on geometric spline quotients -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

private def backendDot (element : DihedralGroup n) :
    (dihedralReflectionData n hthree).LeftQuotient selected.indices ≃ₐ[ℂ]
      (dihedralReflectionData n hthree).LeftQuotient selected.indices :=
  (dihedralGradedReflectionData n hthree).leftQuotientDotEquiv selected.indices element

/-- Dot translation on the geometric coordinate quotient. -/
def dotEquiv (element : DihedralGroup n) : Quotient selected hthree ≃ₐ[ℂ]
    Quotient selected hthree :=
  ((backendEquiv selected hthree).trans
    (backendDot selected hthree element)).trans
    (backendEquiv selected hthree).symm

/-- Quotient dot translation translates any geometric spline representative. -/
theorem dot_map (element : DihedralGroup n) (value : selected.Spline) :
    dotEquiv selected hthree element (quotientMap selected hthree value) =
      quotientMap selected hthree (selected.dot hthree element value) := by
  apply (backendEquiv selected hthree).injective
  change (backendEquiv selected hthree)
      ((backendEquiv selected hthree).symm
        (backendDot selected hthree element
          (backendEquiv selected hthree (quotientMap selected hthree value)))) = _
  rw [AlgEquiv.apply_symm_apply, backendEquiv_map, backendEquiv_map]
  exact (dihedralGradedReflectionData n hthree).leftQuotientDotEquiv_mk
    selected.indices element (selected.backendEquiv hthree value)

/-- The geometric quotient dot automorphisms form a group action. -/
def dotAction : DihedralGroup n →* (Quotient selected hthree ≃ₐ[ℂ]
    Quotient selected hthree) where
  toFun := dotEquiv selected hthree
  map_one' := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨original, rfl⟩ := map_surjective selected hthree value
    simp only [dot_map, RootSubset.dot_one, AlgEquiv.one_apply]
  map_mul' first second := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨original, rfl⟩ := map_surjective selected hthree value
    simp only [AlgEquiv.mul_apply, dot_map, RootSubset.dot_mul]

/-- Quotient dot translation preserves each homogeneous degree piece. -/
theorem dot_mem_piece (element : DihedralGroup n) (degree : ℕ)
    (value : Quotient selected hthree) (hvalue : value ∈ piece selected hthree degree) :
    dotEquiv selected hthree element value ∈ piece selected hthree degree := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  obtain ⟨original, horiginal, rfl⟩ := (mem_piece selected hthree degree value).1 hvalue
  rw [dot_map]
  exact (mem_piece selected hthree degree _).2
    ⟨selected.dot hthree element original,
      selected.dot_mem_piece hthree element degree original horiginal, rfl⟩

/-- The complex dot representation on the whole geometric quotient. -/
def representation : Representation ℂ (DihedralGroup n) (Quotient selected hthree) :=
  (AlgEquiv.toLinearMapHom ℂ _).comp (dotAction selected hthree)

/-- The complex dot representation on a homogeneous geometric quotient piece. -/
def pieceRepresentation (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (piece selected hthree degree) :=
  (representation selected hthree).subrepresentation (piece selected hthree degree)
    fun element value hvalue => dot_mem_piece selected hthree element degree value hvalue

end Left

namespace Right

private def backendDot (element : DihedralGroup n) :
    (dihedralReflectionData n hthree).RightQuotient selected.indices ≃ₐ[ℂ]
      (dihedralReflectionData n hthree).RightQuotient selected.indices :=
  (dihedralGradedReflectionData n hthree).rightQuotientDotEquiv selected.indices element

/-- Dot translation on the geometric coordinate quotient. -/
def dotEquiv (element : DihedralGroup n) : Quotient selected hthree ≃ₐ[ℂ]
    Quotient selected hthree :=
  ((backendEquiv selected hthree).trans
    (backendDot selected hthree element)).trans
    (backendEquiv selected hthree).symm

/-- Quotient dot translation translates any geometric spline representative. -/
theorem dot_map (element : DihedralGroup n) (value : selected.Spline) :
    dotEquiv selected hthree element (quotientMap selected hthree value) =
      quotientMap selected hthree (selected.dot hthree element value) := by
  apply (backendEquiv selected hthree).injective
  change (backendEquiv selected hthree)
      ((backendEquiv selected hthree).symm
        (backendDot selected hthree element
          (backendEquiv selected hthree (quotientMap selected hthree value)))) = _
  rw [AlgEquiv.apply_symm_apply, backendEquiv_map, backendEquiv_map]
  exact (dihedralGradedReflectionData n hthree).rightQuotientDotEquiv_mk
    selected.indices element (selected.backendEquiv hthree value)

/-- The geometric quotient dot automorphisms form a group action. -/
def dotAction : DihedralGroup n →* (Quotient selected hthree ≃ₐ[ℂ]
    Quotient selected hthree) where
  toFun := dotEquiv selected hthree
  map_one' := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨original, rfl⟩ := map_surjective selected hthree value
    simp only [dot_map, RootSubset.dot_one, AlgEquiv.one_apply]
  map_mul' first second := by
    apply AlgEquiv.ext
    intro value
    obtain ⟨original, rfl⟩ := map_surjective selected hthree value
    simp only [AlgEquiv.mul_apply, dot_map, RootSubset.dot_mul]

/-- Quotient dot translation preserves each homogeneous degree piece. -/
theorem dot_mem_piece (element : DihedralGroup n) (degree : ℕ)
    (value : Quotient selected hthree) (hvalue : value ∈ piece selected hthree degree) :
    dotEquiv selected hthree element value ∈ piece selected hthree degree := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  obtain ⟨original, horiginal, rfl⟩ := (mem_piece selected hthree degree value).1 hvalue
  rw [dot_map]
  exact (mem_piece selected hthree degree _).2
    ⟨selected.dot hthree element original,
      selected.dot_mem_piece hthree element degree original horiginal, rfl⟩

/-- The complex dot representation on the whole geometric quotient. -/
def representation : Representation ℂ (DihedralGroup n) (Quotient selected hthree) :=
  (AlgEquiv.toLinearMapHom ℂ _).comp (dotAction selected hthree)

/-- The complex dot representation on a homogeneous geometric quotient piece. -/
def pieceRepresentation (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (piece selected hthree degree) :=
  (representation selected hthree).subrepresentation (piece selected hthree degree)
    fun element value hvalue => dot_mem_piece selected hthree element degree value hvalue

end Right

end Schubert.Dihedral.RootSubset
