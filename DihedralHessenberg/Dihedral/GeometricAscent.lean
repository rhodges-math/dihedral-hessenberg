import DihedralHessenberg.Dihedral.RootAngularEquality
import DihedralHessenberg.Dihedral.InversionAscent

/-! # Positive-root interpretation of simple-ascent inversion updates -/

namespace Schubert.Dihedral

/-- A simple reflection has exactly its own positive root as a right inversion. -/
theorem rightInversions_simple_eq_singleton (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n)
    (hreflection : rootReflection index = simpleReflection n simple) :
    rightInversions n hthree (simpleReflection n simple) = {index} := by
  classical
  have hcard : (rightInversions n hthree (simpleReflection n simple)).card = 1 := by
    rw [card_rightInversions, length_simpleReflection]
  obtain ⟨other, hother⟩ := Finset.card_eq_one.mp hcard
  have hmember : index ∈ rightInversions n hthree (simpleReflection n simple) := by
    rw [mem_rightInversions, ← hreflection, rootReflection_mul_self, length_one,
      hreflection, length_simpleReflection]
    decide
  rw [hother, Finset.mem_singleton] at hmember
  rw [hother, hmember]

/-- A simple left ascent inserts the positive inverse image of its root into right inversions. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.right_ascent_image (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    ∃ image : PositiveRootIndex n,
      vectorOperator n element⁻¹ (complexPositiveRoot n index) = complexPositiveRoot n image ∧
        rightInversions n hthree (simpleReflection n simple * element) =
          insert image (rightInversions n hthree element) ∧
            image ∉ rightInversions n hthree element := by
  classical
  have hnot : index ∉ rightInversions n hthree element⁻¹ := by
    rw [rightInversions_inv_eq_leftInversions, mem_leftInversions, hreflection, hascent]
    omega
  obtain ⟨image, himage, hreflectionImage⟩ :=
    _root_.Schubert.Dihedral.IndexedInversions.positive_image_of_not_mem n hthree element⁻¹ index
      hnot
  rw [inv_inv, hreflection] at hreflectionImage
  refine ⟨image, himage, ?_, ?_⟩
  · apply Finset.image_injective (rootReflection_injective n)
    rw [Finset.image_insert, hreflectionImage,
      image_rightInversions_simple_left_ascent n hthree simple element hascent]
  · intro hmember
    apply _root_.Schubert.Dihedral.IndexedInversions.conjugate_simple_not_mem n hthree simple
      element hascent
    exact Finset.mem_image.mpr ⟨image, hmember, hreflectionImage⟩

private theorem mem_rootReflection_image_iff {n : ℕ} (selected : Finset (PositiveRootIndex n))
    (index : PositiveRootIndex n) :
    rootReflection index ∈ selected.image rootReflection ↔ index ∈ selected := by
  classical
  constructor
  · intro hmember
    obtain ⟨other, hother, heq⟩ := Finset.mem_image.mp hmember
    exact (rootReflection_injective n heq) ▸ hother
  · intro hindex
    exact Finset.mem_image.mpr ⟨index, hindex, rfl⟩

/-- Previous left inversion roots stay positive under a simple left ascent. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.simple_image_of_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1)
    (previous : PositiveRootIndex n) (hprevious : previous ∈ leftInversions n hthree element) :
    ∃ image : PositiveRootIndex n,
      vectorOperator n (simpleReflection n simple) (complexPositiveRoot n previous) =
        complexPositiveRoot n image ∧ rootReflection image =
          (MulAut.conj (simpleReflection n simple)) (rootReflection previous) := by
  have hnot : previous ∉ rightInversions n hthree (simpleReflection n simple) := by
    rw [rightInversions_simple_eq_singleton n hthree simple index hreflection,
      Finset.mem_singleton]
    intro heq
    rw [heq, mem_leftInversions, hreflection, hascent] at hprevious
    omega
  obtain ⟨image, himage, hconj⟩ :=
    _root_.Schubert.Dihedral.IndexedInversions.positive_image_of_not_mem
    n hthree (simpleReflection n simple) previous hnot
  exact ⟨image, himage, hconj⟩

/-- A simple left ascent inserts its root and acts on all previous left inversion roots. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) (image : PositiveRootIndex n) :
    image ∈ leftInversions n hthree (simpleReflection n simple * element) ↔
      image = index ∨ ∃ previous ∈ leftInversions n hthree element,
        vectorOperator n (simpleReflection n simple) (complexPositiveRoot n previous) =
          complexPositiveRoot n image := by
  classical
  let : NeZero n := ⟨by omega⟩
  rw [← mem_rootReflection_image_iff,
    image_leftInversions_simple_left_ascent n hthree simple element hascent,
    Finset.mem_insert]
  constructor
  · rintro (hsimple | hprevious)
    · exact Or.inl (rootReflection_injective n (hsimple.trans hreflection.symm))
    · obtain ⟨reflection, hreflectionMem, heq⟩ := Finset.mem_image.mp hprevious
      obtain ⟨previous, hpreviousMem, hpreviousEq⟩ := Finset.mem_image.mp hreflectionMem
      obtain ⟨other, hotherImage, hotherReflection⟩ :=
        _root_.Schubert.Dihedral.IndexedInversions.simple_image_of_ascent n hthree simple index
          element
          hreflection hascent previous hpreviousMem
      have hindices : other = image := rootReflection_injective n
        (hotherReflection.trans ((congrArg (MulAut.conj (simpleReflection n simple))
          hpreviousEq).trans heq))
      exact Or.inr ⟨previous, hpreviousMem, hindices ▸ hotherImage⟩
  · rintro (rfl | ⟨previous, hprevious, himage⟩)
    · exact Or.inl hreflection
    · apply Or.inr
      have hconj := rootReflection_of_positive_image n (simpleReflection n simple)
        previous image himage
      exact Finset.mem_image.mpr ⟨rootReflection previous,
        Finset.mem_image.mpr ⟨previous, hprevious, rfl⟩, hconj.symm⟩

/-- The inserted root is absent from the transformed previous left inversion roots. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.simple_not_image_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    ¬∃ previous ∈ leftInversions n hthree element,
      vectorOperator n (simpleReflection n simple) (complexPositiveRoot n previous) =
        complexPositiveRoot n index := by
  classical
  let : NeZero n := ⟨by omega⟩
  rintro ⟨previous, hprevious, himage⟩
  apply _root_.Schubert.Dihedral.IndexedInversions.simple_not_mem_conjugate n hthree simple element
    hascent
  have hconj := rootReflection_of_positive_image n (simpleReflection n simple)
    previous index himage
  exact Finset.mem_image.mpr ⟨rootReflection previous,
    Finset.mem_image.mpr ⟨previous, hprevious, rfl⟩, hconj.symm.trans hreflection⟩

/-- On real roots, a simple left ascent inserts its root and transforms old left inversions. -/
theorem real_leftInversions_simple_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    positiveRoot n '' {image | image ∈
      leftInversions n hthree (simpleReflection n simple * element)} =
      {positiveRoot n index} ∪
        (fun vector : RealPlane => fun coordinate =>
          (vectorOperator n (simpleReflection n simple) (complexify vector) coordinate).re) ''
            (positiveRoot n '' {previous | previous ∈ leftInversions n hthree element}) := by
  ext vector
  constructor
  · rintro ⟨image, hmember, rfl⟩
    rcases (_root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem n hthree simple index element
      hreflection hascent image).mp hmember with heq | ⟨previous, hprevious, himage⟩
    · exact Or.inl (by rw [heq]; rfl)
    · apply Or.inr
      refine ⟨positiveRoot n previous, ⟨previous, hprevious, rfl⟩, ?_⟩
      have hreal := congrArg (fun value : ComplexPlane => fun coordinate =>
        (value coordinate).re) himage
      simpa only [complexPositiveRoot, complexify, Complex.ofReal_re] using hreal
  · rintro (heq | ⟨previousVector, ⟨previous, hprevious, rfl⟩, heq⟩)
    · refine ⟨index, ?_, Set.mem_singleton_iff.mp heq |>.symm⟩
      exact (_root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem n hthree simple index
        element
        hreflection hascent index).mpr (Or.inl rfl)
    · obtain ⟨image, himage, _⟩ := _root_.Schubert.Dihedral.IndexedInversions.simple_image_of_ascent
        n hthree simple index element hreflection hascent previous hprevious
      refine ⟨image, ?_, ?_⟩
      · exact (_root_.Schubert.Dihedral.IndexedInversions.left_ascent_mem n hthree simple index
        element
          hreflection hascent image).mpr (Or.inr ⟨previous, hprevious, himage⟩)
      · have hreal := congrArg (fun value : ComplexPlane => fun coordinate =>
          (value coordinate).re) himage
        have hrealImage : (fun coordinate =>
            (vectorOperator n (simpleReflection n simple)
              (complexify (positiveRoot n previous)) coordinate).re) = positiveRoot n image := by
          simpa only [complexPositiveRoot, complexify, Complex.ofReal_re] using hreal
        exact hrealImage.symm.trans heq

/-- On real roots, a simple left ascent inserts its positive inverse image into right inversions. -/
theorem real_rightInversions_simple_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    positiveRoot n '' {image | image ∈
      rightInversions n hthree (simpleReflection n simple * element)} =
      {(fun coordinate =>
        (vectorOperator n element⁻¹ (complexPositiveRoot n index) coordinate).re)} ∪
        (positiveRoot n '' {previous | previous ∈ rightInversions n hthree element}) := by
  obtain ⟨image, himage, hset, _⟩ := _root_.Schubert.Dihedral.IndexedInversions.right_ascent_image
    n hthree simple index element hreflection hascent
  have hreal := congrArg (fun value : ComplexPlane => fun coordinate =>
    (value coordinate).re) himage
  have hrealImage : (fun coordinate =>
      (vectorOperator n element⁻¹ (complexPositiveRoot n index) coordinate).re) =
        positiveRoot n image := by
    simpa only [complexPositiveRoot, complexify, Complex.ofReal_re] using hreal
  rw [hrealImage]
  ext vector
  simp [hset, Set.mem_image, eq_comm, or_and_right, exists_or]

/-- The simple root does not occur among the real transformed old left inversions. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.simple_not_mem_image (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    positiveRoot n index ∉
      (fun vector : RealPlane => fun coordinate =>
        (vectorOperator n (simpleReflection n simple) (complexify vector) coordinate).re) ''
          (positiveRoot n '' {previous | previous ∈ leftInversions n hthree element}) := by
  rintro ⟨previousVector, ⟨previous, hprevious, rfl⟩, heq⟩
  obtain ⟨image, himage, _⟩ := _root_.Schubert.Dihedral.IndexedInversions.simple_image_of_ascent
    n hthree simple index element hreflection hascent previous hprevious
  have hreal := congrArg (fun value : ComplexPlane => fun coordinate =>
    (value coordinate).re) himage
  have hrealImage : (fun coordinate =>
      (vectorOperator n (simpleReflection n simple)
        (complexify (positiveRoot n previous)) coordinate).re) = positiveRoot n image := by
    simpa only [complexPositiveRoot, complexify, Complex.ofReal_re] using hreal
  have hindices := positiveRoot_injective n (hrealImage.symm.trans heq)
  apply _root_.Schubert.Dihedral.IndexedInversions.simple_not_image_ascent n hthree simple index
    element
    hreflection hascent
  exact ⟨previous, hprevious, hindices ▸ himage⟩

/-- The inserted real inverse image is absent from the previous right inversion roots. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.simple_inverse_not_mem (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    (fun coordinate =>
      (vectorOperator n element⁻¹ (complexPositiveRoot n index) coordinate).re) ∉
        positiveRoot n '' {previous | previous ∈ rightInversions n hthree element} := by
  obtain ⟨image, himage, _, hnot⟩ := _root_.Schubert.Dihedral.IndexedInversions.right_ascent_image
    n hthree simple index element hreflection hascent
  have hreal := congrArg (fun value : ComplexPlane => fun coordinate =>
    (value coordinate).re) himage
  have hrealImage : (fun coordinate =>
      (vectorOperator n element⁻¹ (complexPositiveRoot n index) coordinate).re) =
        positiveRoot n image := by
    simpa only [complexPositiveRoot, complexify, Complex.ofReal_re] using hreal
  rw [hrealImage]
  rintro ⟨previous, hprevious, heq⟩
  exact hnot ((positiveRoot_injective n heq) ▸ hprevious)

end Schubert.Dihedral
