import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Dihedral.ConeCoordinates
import Mathlib.Tactic
import Mathlib.Algebra.Group.Fin.Tuple
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Rank-two positive root vectors and their simple-root lattice order -/

noncomputable section

namespace Schubert.Dihedral

private theorem scaled_simple_independent (n : ℕ) (hthree : 3 ≤ n)
    (first second : ℝ) (hfirst : first ≠ 0) (hsecond : second ≠ 0) :
    LinearIndependent ℝ ![first • (simpleRoot n hthree 0).val,
      second • (simpleRoot n hthree 1).val] := by
  have hzero : (simpleRoot n hthree 0).val = ![1, 0] := by
    rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
    simp [unitRootAt]
  have hone : (simpleRoot n hthree 1).val =
      ![-Real.cos (Real.pi / n), Real.sin (Real.pi / n)] := by
    rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
    simp only [unitRootAt, Real.cos_pi_sub, Real.sin_pi_sub]
  rw [hzero, hone]
  apply LinearIndependent.pair_iffₛ.mpr
  intro left right left' right' heq
  have hcoordinate := congrArg (fun vector : RealPlane => vector 1) heq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, zero_add] at hcoordinate
  have hsin := (fundamentalAngle_sin_pos n hthree).ne'
  have hright : right = right' :=
    mul_right_cancel₀ (mul_ne_zero hsecond hsin) (by nlinarith [hcoordinate])
  have hcoordinate := congrArg (fun vector : RealPlane => vector 0) heq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    mul_one, hright] at hcoordinate
  have hleft : left = left' := mul_right_cancel₀ hfirst (by nlinarith [hcoordinate])
  exact ⟨hleft, hright⟩

/-- Positive root vectors together with their two simple vectors. -/
structure RootLattice where
  /-- The first simple vector. -/
  first : RealPlane
  /-- The second simple vector. -/
  second : RealPlane
  /-- The positive root vectors. -/
  positive : Set RealPlane

namespace RootLattice

/-- The complete signed root vectors obtained from a positive configuration. -/
def roots (lattice : RootLattice) : Set RealPlane :=
  lattice.positive ∪ {vector | -vector ∈ lattice.positive}

/-- Root comparison means that the difference is a nonnegative integer simple-root sum. -/
def LE (lattice : RootLattice) (alpha beta : RealPlane) : Prop :=
  ∃ first second : ℕ,
    beta - alpha = (first : ℝ) • lattice.first + (second : ℝ) • lattice.second

/-- Integer simple-root comparison is reflexive. -/
theorem refl (lattice : RootLattice) (alpha : RealPlane) : lattice.LE alpha alpha := by
  exact ⟨0, 0, by simp⟩

/-- Integer simple-root comparison is transitive. -/
theorem trans (lattice : RootLattice) {alpha beta gamma : RealPlane}
    (hfirst : lattice.LE alpha beta) (hsecond : lattice.LE beta gamma) :
    lattice.LE alpha gamma := by
  obtain ⟨first, second, hfirst⟩ := hfirst
  obtain ⟨third, fourth, hsecond⟩ := hsecond
  refine ⟨first + third, second + fourth, ?_⟩
  rw [Nat.cast_add, Nat.cast_add, add_smul, add_smul]
  have hsum : gamma - alpha = (beta - alpha) + (gamma - beta) := by abel
  rw [hsum, hfirst, hsecond]
  abel

/-- Independent simple roots compare integer combinations coordinatewise. -/
theorem le_coefficients (lattice : RootLattice)
    (hindependent : LinearIndependent ℝ ![lattice.first, lattice.second])
    (first second third fourth : ℕ) :
    lattice.LE ((first : ℝ) • lattice.first + (second : ℝ) • lattice.second)
        ((third : ℝ) • lattice.first + (fourth : ℝ) • lattice.second) ↔
      first ≤ third ∧ second ≤ fourth := by
  constructor
  · rintro ⟨left, right, heq⟩
    have hsum : (third : ℝ) • lattice.first + (fourth : ℝ) • lattice.second =
        ((first + left : ℕ) : ℝ) • lattice.first +
          ((second + right : ℕ) : ℝ) • lattice.second := by
      rw [Nat.cast_add, Nat.cast_add, add_smul, add_smul]
      have hsum := congrArg (fun vector =>
        vector + ((first : ℝ) • lattice.first + (second : ℝ) • lattice.second)) heq
      simpa only [sub_add_cancel] using hsum.trans (by abel)
    obtain ⟨hfirst, hsecond⟩ := hindependent.eq_of_pair hsum
    have hfirst : third = first + left := Nat.cast_injective hfirst
    have hsecond : fourth = second + right := Nat.cast_injective hsecond
    omega
  · rintro ⟨hfirst, hsecond⟩
    refine ⟨third - first, fourth - second, ?_⟩
    rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond, sub_smul, sub_smul]
    abel

/-- The rank-two A positive vectors have equal simple-root lengths. -/
def a2 : RootLattice :=
  let first := (simpleRoot 3 (by decide) 0).val
  let second := (simpleRoot 3 (by decide) 1).val
  ⟨first, second, {first, second, first + second}⟩

/-- The rank-two B positive vectors with the first simple root short. -/
def b2 : RootLattice :=
  let first := (simpleRoot 4 (by decide) 0).val
  let second := Real.sqrt 2 • (simpleRoot 4 (by decide) 1).val
  ⟨first, second, {first, second, first + second, (2 : ℝ) • first + second}⟩

/-- The rank-two C positive vectors with the second simple root short. -/
def c2 : RootLattice :=
  let first := Real.sqrt 2 • (simpleRoot 4 (by decide) 0).val
  let second := (simpleRoot 4 (by decide) 1).val
  ⟨first, second, {first, second, first + second, first + (2 : ℝ) • second}⟩

/-- The rank-two G positive vectors with the first simple root short. -/
def g2 : RootLattice :=
  let first := (simpleRoot 6 (by decide) 0).val
  let second := Real.sqrt 3 • (simpleRoot 6 (by decide) 1).val
  ⟨first, second, {first, second, first + second, (2 : ℝ) • first + second,
    (3 : ℝ) • first + second, (3 : ℝ) • first + (2 : ℝ) • second}⟩

/-- The A simple vectors form an independent pair. -/
theorem a2_independent : LinearIndependent ℝ ![a2.first, a2.second] := by
  simpa only [a2, one_smul] using
    scaled_simple_independent 3 (by decide) 1 1 (by norm_num) (by norm_num)

/-- The B simple vectors form an independent pair. -/
theorem b2_independent : LinearIndependent ℝ ![b2.first, b2.second] := by
  simpa only [b2, one_smul] using scaled_simple_independent 4 (by decide) 1 (Real.sqrt 2)
    (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- The C simple vectors form an independent pair. -/
theorem c2_independent : LinearIndependent ℝ ![c2.first, c2.second] := by
  simpa only [c2, one_smul] using scaled_simple_independent 4 (by decide) (Real.sqrt 2) 1
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (by norm_num)

/-- The G simple vectors form an independent pair. -/
theorem g2_independent : LinearIndependent ℝ ![g2.first, g2.second] := by
  simpa only [g2, one_smul] using scaled_simple_independent 6 (by decide) 1 (Real.sqrt 3)
    (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- The first short B simple root is the horizontal unit vector. -/
theorem b2_first : b2.first = ![1, 0] := by
  change (simpleRoot 4 (by decide) 0).val = _
  rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
  simp [unitRootAt]

/-- The long B simple root has integral planar coordinates. -/
theorem b2_second : b2.second = ![-1, 1] := by
  change Real.sqrt 2 • (simpleRoot 4 (by decide) 1).val = _
  rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
  simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsquare : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply realPlane_ext
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    nlinarith
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith

/-- The B positive roots have the standard integral planar coordinates. -/
theorem b2_positive : b2.positive = {![1, 0], ![-1, 1], ![0, 1], ![1, 1]} := by
  have hset : b2.positive = {b2.first, b2.second, b2.first + b2.second,
      (2 : ℝ) • b2.first + b2.second} := rfl
  rw [hset, b2_first, b2_second]
  have hsum : (![1, 0] : RealPlane) + ![-1, 1] = ![0, 1] := by
    apply realPlane_ext <;> norm_num [Pi.add_apply]
  have htwice : (2 : ℝ) • (![1, 0] : RealPlane) + ![-1, 1] = ![1, 1] := by
    apply realPlane_ext <;> norm_num [Pi.add_apply, Pi.smul_apply]
  rw [hsum, htwice]

/-- The B simple roots have the standard asymmetric integral Cartan entries. -/
theorem b2_cartan :
    2 * realBilinearForm b2.second b2.first / realBilinearForm b2.first b2.first = -2 ∧
      2 * realBilinearForm b2.first b2.second / realBilinearForm b2.second b2.second = -1 := by
  rw [b2_first, b2_second]
  norm_num [realBilinearForm]

/-- The first long C simple root is the horizontal vector of length square root two. -/
theorem c2_first : c2.first = ![Real.sqrt 2, 0] := by
  change Real.sqrt 2 • (simpleRoot 4 (by decide) 0).val = _
  rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
  apply realPlane_ext <;> simp [unitRootAt]

/-- The short C simple root is the diagonal unit vector. -/
theorem c2_second : c2.second = ![-Real.sqrt 2 / 2, Real.sqrt 2 / 2] := by
  change (simpleRoot 4 (by decide) 1).val = _
  rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
  simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_four, Real.sin_pi_div_four, neg_div]

/-- The first short G simple root is the horizontal unit vector. -/
theorem g2_first : g2.first = ![1, 0] := by
  change (simpleRoot 6 (by decide) 0).val = _
  rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
  simp [unitRootAt]

/-- The long G simple root has the standard coordinates with squared length three. -/
theorem g2_second : g2.second = ![-3 / 2, Real.sqrt 3 / 2] := by
  change Real.sqrt 3 • (simpleRoot 6 (by decide) 1).val = _
  rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
  simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  have hsquare : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  apply realPlane_ext
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    nlinarith
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring

/-- The A simple roots have their standard unit coordinates. -/
theorem a2_coordinates : a2.first = ![1, 0] ∧
    a2.second = ![-1 / 2, Real.sqrt 3 / 2] := by
  constructor
  · change (simpleRoot 3 (by decide) 0).val = _
    rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
    simp [unitRootAt]
  · change (simpleRoot 3 (by decide) 1).val = _
    rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
    simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three, neg_div]

/-- The A configuration is exactly the three positive unit root vectors. -/
theorem a2_positive : a2.positive = positiveRoots 3 := by
  have hzero : positiveRoot 3 ⟨0, by decide⟩ = a2.first := by
    change _ = (simpleRoot 3 (by decide) 0).val
    rw [simpleRoot_zero, positiveRootEquiv_val]
    rfl
  have hone : positiveRoot 3 ⟨1, by decide⟩ = a2.second := by
    change _ = (simpleRoot 3 (by decide) 1).val
    rw [simpleRoot_one, positiveRootEquiv_val]
    rfl
  have htwo : positiveRoot 3 ⟨2, by decide⟩ = a2.first + a2.second := by
    rw [a2_coordinates.1, a2_coordinates.2]
    norm_num [positiveRoot, rootAngle, unitRootAt, Real.cos_pi_div_three,
      Real.sin_pi_div_three, Pi.add_apply]
  have hset : a2.positive = {a2.first, a2.second, a2.first + a2.second} := rfl
  rw [hset]
  ext vector
  constructor
  · intro hmem
    rcases hmem with rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, hzero⟩
    · exact ⟨⟨1, by decide⟩, hone⟩
    · exact ⟨⟨2, by decide⟩, htwo⟩
  · rintro ⟨index, rfl⟩
    fin_cases index <;> simp only [hzero, hone, htwo, Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals tauto

/-- The complete B roots are the eight standard integral planar vectors. -/
theorem b2_roots : b2.roots =
    {![1, 0], ![-1, 1], ![0, 1], ![1, 1],
      ![-1, 0], ![1, -1], ![0, -1], ![-1, -1]} := by
  rw [roots, b2_positive]
  ext vector
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    neg_eq_iff_eq_neg]
  norm_num only [Matrix.neg_cons, Matrix.neg_empty, neg_neg, neg_zero]
  tauto

/-- Every normal reflection in a B root preserves the complete vector set. -/
theorem b2_reflection_mem (normal vector : RealPlane) (hnormal : normal ∈ b2.roots)
    (hvector : vector ∈ b2.roots) :
    vector - (2 * realBilinearForm vector normal /
      realBilinearForm normal normal) • normal ∈ b2.roots := by
  rw [b2_roots] at hnormal hvector ⊢
  rcases hnormal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hvector with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [realBilinearForm, Matrix.smul_cons, Matrix.sub_cons] <;>
    simp [← Matrix.zero_empty]

/-- Every B root has strictly positive squared length. -/
theorem b2_norm_pos (vector : RealPlane) (hvector : vector ∈ b2.roots) :
    0 < realBilinearForm vector vector := by
  rw [b2_roots] at hvector
  rcases hvector with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [realBilinearForm]

/-- B root-coroot pairings are integral for every pair of signed vectors. -/
theorem b2_integral (normal vector : RealPlane) (hnormal : normal ∈ b2.roots)
    (hvector : vector ∈ b2.roots) :
    ∃ integer : ℤ, 2 * realBilinearForm vector normal /
      realBilinearForm normal normal = (integer : ℝ) := by
  rw [b2_roots] at hnormal hvector
  rcases hnormal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hvector with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals solve
    | refine ⟨-2, ?_⟩; norm_num [realBilinearForm]
    | refine ⟨-1, ?_⟩; norm_num [realBilinearForm]
    | refine ⟨0, ?_⟩; norm_num [realBilinearForm]
    | refine ⟨1, ?_⟩; norm_num [realBilinearForm]
    | refine ⟨2, ?_⟩; norm_num [realBilinearForm]

end RootLattice

end Schubert.Dihedral
