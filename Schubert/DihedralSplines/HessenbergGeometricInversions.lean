import Schubert.Dihedral.RootInversionSigns
import Schubert.DihedralSplines.HessenbergInversions

/-! # Geometric signs of canonical and Hessenberg inversions -/

namespace Schubert.Dihedral

/-- A realized root image is the complexification of its real coordinates. -/
theorem complexify_realRootImage (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (vector : RealPlane) (hroot : vector ∈ roots n) :
    complexify (fun coordinate =>
      (vectorOperator n element (complexify vector) coordinate).re) =
        vectorOperator n element (complexify vector) := by
  obtain ⟨image, _, heq⟩ := vectorOperator_complexify_mem_roots n element vector hroot
  simp only [heq, complexify, Complex.ofReal_re]

/-- The action followed by negation distinguishes the positive-root indices. -/
theorem negative_root_image_injective (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    Function.Injective (fun index : PositiveRootIndex n =>
      -(fun coordinate =>
        (vectorOperator n element (complexPositiveRoot n index) coordinate).re)) := by
  intro first second heq
  have hreal := neg_injective heq
  have hcomplex := congrArg complexify hreal
  have hfirst := complexify_realRootImage n element (positiveRoot n first)
    (Or.inl ⟨first, rfl⟩)
  have hsecond := complexify_realRootImage n element (positiveRoot n second)
    (Or.inl ⟨second, rfl⟩)
  change complexify (fun coordinate =>
    (vectorOperator n element (complexPositiveRoot n first) coordinate).re) =
      vectorOperator n element (complexPositiveRoot n first) at hfirst
  change complexify (fun coordinate =>
    (vectorOperator n element (complexPositiveRoot n second) coordinate).re) =
      vectorOperator n element (complexPositiveRoot n second) at hsecond
  rw [hfirst, hsecond] at hcomplex
  have hinverse := congrArg (vectorOperator n element⁻¹) hcomplex
  simp only [← LinearMap.comp_apply, ← vectorOperator_mul, inv_mul_cancel,
    vectorOperator_one, LinearMap.id_apply] at hinverse
  exact positiveRoot_injective n (complexify_injective hinverse)

/-- Canonical left inversions are positive roots with negative image under the inverse. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.left_negative_iff (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (index : PositiveRootIndex n) :
    index ∈ leftInversions n hthree element ↔
      -(fun coordinate =>
        (vectorOperator n element⁻¹ (complexPositiveRoot n index) coordinate).re) ∈
          positiveRoots n := by
  rw [← rightInversions_inv_eq_leftInversions, mem_rightInversions_iff_negative_image]

/-- Negating a root image agrees with applying the representation to the negative root. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.negative_image_eq (n : ℕ) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    -(fun coordinate =>
      (vectorOperator n element (complexPositiveRoot n index) coordinate).re) =
      fun coordinate =>
        (vectorOperator n element (complexify (-positiveRoot n index)) coordinate).re := by
  have hcomplex : complexify (-positiveRoot n index) = -complexPositiveRoot n index := by
    funext coordinate
    simp [complexify, complexPositiveRoot]
  rw [hcomplex, map_neg]
  rfl

/-- For any selected positive roots, negative images identify inversions with positive images. -/
theorem selected_negative_image_bijOn (n : ℕ) (hthree : 3 ≤ n)
    (selected : Set (PositiveRootIndex n)) (element : DihedralGroup n) :
    Set.BijOn
      (fun index : PositiveRootIndex n =>
        -(fun coordinate =>
          (vectorOperator n element (complexPositiveRoot n index) coordinate).re))
      (selected ∩ {index | index ∈ rightInversions n hthree element})
      ((fun index : PositiveRootIndex n =>
        -(fun coordinate =>
          (vectorOperator n element (complexPositiveRoot n index) coordinate).re)) ''
        selected ∩ positiveRoots n) := by
  let : NeZero n := ⟨by omega⟩
  refine ⟨?_, (negative_root_image_injective n element).injOn, ?_⟩
  · intro index hindex
    exact ⟨⟨index, hindex.1, rfl⟩,
      (mem_rightInversions_iff_negative_image n hthree element index).mp hindex.2⟩
  · intro vector hvector
    obtain ⟨⟨index, hindex, heq⟩, hpositive⟩ := hvector
    change -(fun coordinate =>
      (vectorOperator n element (complexPositiveRoot n index) coordinate).re) = vector at heq
    refine ⟨index, ⟨hindex, ?_⟩, heq⟩
    exact (mem_rightInversions_iff_negative_image n hthree element index).mpr
      (heq.symm ▸ hpositive)

end Schubert.Dihedral

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

/-- H-inversions are precisely the roots in H whose realized images are negative. -/
theorem mem_inversions_iff_negative_image {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    index ∈ ideal.inversions element ↔ index ∈ ideal.roots ∧
      -(fun coordinate =>
        (vectorOperator n element (complexPositiveRoot n index) coordinate).re) ∈
          positiveRoots n := by
  classical
  simp only [inversions, Finset.mem_inter, mem_rightInversions_iff_negative_image]

/-- Negating the action gives the paper's bijection from H-inversions to positive images of -H. -/
theorem negative_image_bijOn {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) (element : DihedralGroup n) :
    Set.BijOn
      (fun index : PositiveRootIndex n =>
        -(fun coordinate =>
          (vectorOperator n element (complexPositiveRoot n index) coordinate).re))
      {index | index ∈ ideal.inversions element}
      ((fun index : PositiveRootIndex n =>
        -(fun coordinate =>
          (vectorOperator n element (complexPositiveRoot n index) coordinate).re)) ''
        {index | index ∈ ideal.roots} ∩ positiveRoots n) := by
  classical
  have hdomain : {index | index ∈ ideal.inversions element} =
      {index | index ∈ ideal.roots} ∩ {index | index ∈ rightInversions n hthree element} := by
    ext index
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, inversions, Finset.mem_inter]
  rw [hdomain]
  exact selected_negative_image_bijOn n hthree {index | index ∈ ideal.roots} element

end Schubert.DihedralSplines.HessenbergSpace
