import Schubert.Dihedral.ClosestRoots
import Schubert.Dihedral.HyperplaneDistance
import Schubert.Dihedral.RootGenerators
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Simple-root frames in arbitrary generic positive chambers -/

noncomputable section

namespace Schubert.Dihedral.Separator

/-- A group translate identifying a generic chamber with the canonical positive roots. -/
structure Frame {n : ℕ} (data : Separator n) where
  /-- The translating group element. -/
  element : DihedralGroup n
  /-- The positive carrier is exactly the image of the canonical positive vectors. -/
  image : data.positive = realAction n element '' positiveRoots n

namespace Frame

variable {n : ℕ} {data : Separator n} (frame : Frame data)

/-- Every canonical root becomes a positive vector in the translated chamber. -/
def root (alpha : PositiveRoot n) : data.Positive :=
  ⟨realAction n frame.element alpha.val, by
    rw [frame.image]
    exact ⟨alpha.val, alpha.property, rfl⟩⟩

/-- The first simple vector in the generic positive chamber. -/
def first (hthree : 3 ≤ n) : data.Positive := frame.root (simpleRoot n hthree 0)

/-- The second simple vector in the generic positive chamber. -/
def second (hthree : 3 ≤ n) : data.Positive := frame.root (simpleRoot n hthree 1)

/-- The simple vectors in a chamber are distinct. -/
theorem first_ne_second (hthree : 3 ≤ n) :
    (frame.first hthree).val ≠ (frame.second hthree).val := by
  let : NeZero n := ⟨by omega⟩
  intro heq
  change realAction n frame.element (simpleRoot n hthree 0).val =
    realAction n frame.element (simpleRoot n hthree 1).val at heq
  have hvector := (realLinearEquiv n frame.element).injective heq
  have hroot := Subtype.ext hvector
  rw [simpleRoot_zero, simpleRoot_one] at hroot
  have hindex := (positiveRootEquiv n).injective hroot
  have hval := congrArg Fin.val hindex
  norm_num [firstSimpleRootIndex, secondSimpleRootIndex] at hval

/-- Root transport conjugates its corresponding group reflection. -/
theorem reflection_root (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    (data.reflectionEquiv hthree (frame.root alpha)).val =
      frame.element * alpha.reflection * frame.element⁻¹ := by
  let : NeZero n := ⟨by omega⟩
  let beta := (data.rootEquiv hthree).symm (frame.root alpha)
  have hchoose : data.choose beta = frame.root alpha :=
    (data.rootEquiv hthree).apply_symm_apply _
  have hreflection : (data.reflectionEquiv hthree (frame.root alpha)).val = beta.reflection := by
    rw [← hchoose, data.reflection_choose]
  rw [hreflection]
  apply PositiveRoot.signed_conjugation
  have hvector := congrArg Subtype.val hchoose
  unfold choose at hvector
  split_ifs at hvector
  · exact Or.inl hvector.symm
  · exact Or.inr hvector.symm

/-- The first chamber reflection is the conjugate of the first canonical generator. -/
theorem first_reflection (hthree : 3 ≤ n) :
    (data.reflectionEquiv hthree (frame.first hthree)).val =
      frame.element * (simpleRoot n hthree 0).reflection * frame.element⁻¹ :=
  frame.reflection_root hthree _

/-- The second chamber reflection is the conjugate of the second canonical generator. -/
theorem second_reflection (hthree : 3 ≤ n) :
    (data.reflectionEquiv hthree (frame.second hthree)).val =
      frame.element * (simpleRoot n hthree 1).reflection * frame.element⁻¹ :=
  frame.reflection_root hthree _

/-- The reflections of both chamber simple vectors generate the entire group. -/
theorem generate (hthree : 3 ≤ n) :
    Subgroup.closure {(data.reflectionEquiv hthree (frame.first hthree)).val,
      (data.reflectionEquiv hthree (frame.second hthree)).val} = ⊤ := by
  let hom : DihedralGroup n →* DihedralGroup n :=
    { toFun := fun element => frame.element * element * frame.element⁻¹
      map_one' := by group
      map_mul' := by intro first second; group }
  have hsurj : Function.Surjective hom := by
    intro element
    refine ⟨frame.element⁻¹ * element * frame.element, ?_⟩
    dsimp [hom]
    group
  have hgen := congrArg (Subgroup.map hom) (simple_roots_generate n hthree)
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr hsurj] at hgen
  rw [frame.first_reflection, frame.second_reflection]
  exact hgen

/-- Both chamber simple vectors are strictly nearer than every other positive root. -/
theorem closest (hthree : 3 ≤ n) (vector : data.Positive)
    (hfirst : vector.val ≠ (frame.first hthree).val)
    (hsecond : vector.val ≠ (frame.second hthree).val) :
    max (data.distance (frame.first hthree).val) (data.distance (frame.second hthree).val) <
      data.distance vector.val := by
  let : NeZero n := ⟨by omega⟩
  rcases vector with ⟨vector, hmem⟩
  have hpositive_vector := hmem
  rw [frame.image] at hmem
  obtain ⟨normal, hnormal, heq⟩ := hmem
  let alpha : PositiveRoot n := ⟨normal, hnormal⟩
  have ha : alpha ≠ simpleRoot n hthree 0 := by
    intro halpha
    apply hfirst
    change vector = (frame.first hthree).val
    rw [← heq]
    exact congrArg (realAction n frame.element) (congrArg Subtype.val halpha)
  have hb : alpha ≠ simpleRoot n hthree 1 := by
    intro hbeta
    apply hsecond
    change vector = (frame.second hthree).val
    rw [← heq]
    exact congrArg (realAction n frame.element) (congrArg Subtype.val hbeta)
  have hpositive := data.positive_pullback frame.element frame.image
  have hlt := (data.pullback frame.element).simple_extremal hthree hpositive alpha ha hb
  have hfirst_lt : realBilinearForm (frame.first hthree).val data.normal <
      realBilinearForm vector data.normal := by
    have h := lt_of_le_of_lt (le_max_left _ _) hlt
    change realBilinearForm (simpleRoot n hthree 0).val
      (data.transposeNormal frame.element) <
        realBilinearForm normal (data.transposeNormal frame.element) at h
    rw [data.transpose_pairing, data.transpose_pairing, heq] at h
    exact h
  have hsecond_lt : realBilinearForm (frame.second hthree).val data.normal <
      realBilinearForm vector data.normal := by
    have h := lt_of_le_of_lt (le_max_right _ _) hlt
    change realBilinearForm (simpleRoot n hthree 1).val
      (data.transposeNormal frame.element) <
        realBilinearForm normal (data.transposeNormal frame.element) at h
    rw [data.transpose_pairing, data.transpose_pairing, heq] at h
    exact h
  exact max_lt ((data.distance_lt hthree _ _ (frame.first hthree).property
      hpositive_vector).mpr hfirst_lt)
    ((data.distance_lt hthree _ _ (frame.second hthree).property
      hpositive_vector).mpr hsecond_lt)

/-- The unique nearest pair consists of both chamber simple vectors. -/
theorem nearest_pair (hthree : 3 ≤ n) (pair : Finset RealPlane)
    (hpair : pair.card = 2 ∧ (↑pair : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ pair, ∀ second ∈ data.positive, second ∉ pair →
        data.distance first < data.distance second) :
    pair = {(frame.first hthree).val, (frame.second hthree).val} := by
  classical
  let chosen : Finset RealPlane := {(frame.first hthree).val, (frame.second hthree).val}
  have hchosen : chosen.card = 2 ∧ (↑chosen : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ chosen, ∀ second ∈ data.positive, second ∉ chosen →
        data.distance first < data.distance second := by
    have hmem (vector : RealPlane) : vector ∈ chosen ↔
        vector = (frame.first hthree).val ∨ vector = (frame.second hthree).val := by
      simp [chosen]
    refine ⟨by simp [chosen, frame.first_ne_second hthree], ?_, ?_⟩
    · intro vector hvector
      rcases (hmem _).mp hvector with rfl | rfl
      · exact (frame.first hthree).property
      · exact (frame.second hthree).property
    · intro first hfirst second hsecond hout
      have hne_first : second ≠ (frame.first hthree).val := by
        intro heq
        exact hout ((hmem _).mpr (Or.inl heq))
      have hne_second : second ≠ (frame.second hthree).val := by
        intro heq
        exact hout ((hmem _).mpr (Or.inr heq))
      have hlt := frame.closest hthree ⟨second, hsecond⟩ hne_first hne_second
      rcases (hmem _).mp hfirst with rfl | rfl
      · exact lt_of_le_of_lt (le_max_left _ _) hlt
      · exact lt_of_le_of_lt (le_max_right _ _) hlt
  obtain ⟨rootPair, hrootPair, hunique⟩ := data.unique_nearest_pair hthree
  exact (hunique pair hpair).trans (hunique chosen hchosen).symm

end Frame

/-- No single generic positive-root reflection generates the whole dihedral group. -/
theorem singleton_ne_top {n : ℕ} (data : Separator n) (hthree : 3 ≤ n)
    (alpha : data.Positive) :
    Subgroup.closure {(data.reflectionEquiv hthree alpha).val} ≠ ⊤ := by
  let beta := (data.rootEquiv hthree).symm alpha
  have hchoose : data.choose beta = alpha := (data.rootEquiv hthree).apply_symm_apply alpha
  rw [← hchoose, data.reflection_choose]
  exact beta.subgroup_ne_top hthree

/-- Every generic separator has a simple-root frame. -/
def frame {n : ℕ} (data : Separator n) (hthree : 3 ≤ n) : Frame data :=
  ⟨(data.exists_chamber hthree).choose, (data.exists_chamber hthree).choose_spec⟩

end Schubert.Dihedral.Separator
