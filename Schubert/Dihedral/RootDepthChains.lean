import Schubert.Dihedral.RootDepthLayers
import Schubert.Dihedral.RootDepthOrder
import Schubert.Dihedral.SimpleRootPermutation

/-! # The increasing-depth steps between positive roots -/

namespace Schubert.Dihedral

private theorem positive_simple_image {n : ℕ} (hthree : 3 ≤ n) (simple : Fin 2)
    (alpha beta : PositiveRoot n) (hne : alpha ≠ simpleRoot n hthree simple)
    (hconjugate : (simpleRoot n hthree simple).reflection * alpha.reflection *
      (simpleRoot n hthree simple).reflection⁻¹ = beta.reflection) :
    realAction n (simpleRoot n hthree simple).reflection alpha.val = beta.val := by
  let : NeZero n := ⟨by omega⟩
  have hval : alpha.val ≠ (simpleRoot n hthree simple).val :=
    fun heq => hne (Subtype.ext heq)
  have himage := (simple_except_bijOn n hthree simple).mapsTo
    ⟨alpha.property, by simpa only [Set.mem_singleton_iff] using hval⟩
  let image : PositiveRoot n :=
    ⟨realAction n (simpleRoot n hthree simple).reflection alpha.val, himage.1⟩
  have hreflection := PositiveRoot.signed_conjugation
    (simpleRoot n hthree simple).reflection alpha image (Or.inl rfl)
  exact congrArg Subtype.val (PositiveRoot.reflection_injective n
    (hreflection.trans hconjugate))

private theorem simple_image {n : ℕ} (hthree : 3 ≤ n) (simple : Fin 2)
    (index target : Fin n) (hne : index.val ≠ simple.val)
    (hangle : (angularIndex target : ZMod n) =
      -(angularIndex index : ZMod n) - 2 * (simple.val : ZMod n)) :
    realAction n (simpleRoot n hthree simple).reflection (positiveRoot n index) =
      positiveRoot n target := by
  apply positive_simple_image hthree simple (positiveRootEquiv n index)
    (positiveRootEquiv n target)
  · intro heq
    have hindices := congrArg PositiveRoot.index heq
    rw [PositiveRoot.index_equiv] at hindices
    fin_cases simple
    · change index = (simpleRoot n hthree 0).index at hindices
      rw [simpleRoot_zero, PositiveRoot.index_equiv] at hindices
      exact hne (congrArg Fin.val hindices)
    · change index = (simpleRoot n hthree 1).index at hindices
      rw [simpleRoot_one, PositiveRoot.index_equiv] at hindices
      exact hne (congrArg Fin.val hindices)
  · rw [simpleRoot_reflection, PositiveRoot.reflection_equiv,
      PositiveRoot.reflection_equiv, rootReflection_eq_sr_neg_angularIndex,
      rootReflection_eq_sr_neg_angularIndex]
    fin_cases simple
    · change DihedralGroup.sr 0 * DihedralGroup.sr (-(angularIndex index : ZMod n)) *
        (DihedralGroup.sr 0)⁻¹ = DihedralGroup.sr (-(angularIndex target : ZMod n))
      norm_num only at hangle
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
      congr 1
      rw [hangle]; ring
    · change DihedralGroup.sr 1 * DihedralGroup.sr (-(angularIndex index : ZMod n)) *
        (DihedralGroup.sr 1)⁻¹ = DihedralGroup.sr (-(angularIndex target : ZMod n))
      norm_num only at hangle
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
      congr 1
      rw [hangle]; ring

/-- A nonterminal even-indexed root ascends by the second simple reflection. -/
theorem depth_step_even {n : ℕ} (hthree : 3 ≤ n) (index : Fin n)
    (heven : index.val % 2 = 0) (hnext : index.val + 3 < n) :
    DepthStep hthree (positiveRootEquiv n index)
      (positiveRootEquiv n ⟨index.val + 3, hnext⟩) := by
  refine ⟨simpleRoot n hthree 1, Or.inr rfl, ?_, ?_⟩
  · apply simple_image hthree 1 index ⟨index.val + 3, hnext⟩ (by omega)
    have hodd : (index.val + 3) % 2 ≠ 0 := by omega
    simp only [angularIndex, ite_eq_left heven, ite_eq_right hodd]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self,
      Nat.cast_one, Fin.val_one, Nat.cast_one]
    have hdiv : (index.val + 3) / 2 = index.val / 2 + 1 := by omega
    rw [hdiv, Nat.cast_add, Nat.cast_one]
    ring
  · rw [PositiveRoot.depth_layer, PositiveRoot.depth_layer, PositiveRoot.index_equiv,
      PositiveRoot.index_equiv]
    change (index.val + 3) / 2 + 1 = index.val / 2 + 1 + 1
    omega

/-- An odd-indexed root ascends by the first simple reflection. -/
theorem depth_step_odd {n : ℕ} (hthree : 3 ≤ n) (index : Fin n)
    (hodd : index.val % 2 ≠ 0) (hnext : index.val + 1 < n) :
    DepthStep hthree (positiveRootEquiv n index)
      (positiveRootEquiv n ⟨index.val + 1, hnext⟩) := by
  refine ⟨simpleRoot n hthree 0, Or.inl rfl, ?_, ?_⟩
  · apply simple_image hthree 0 index ⟨index.val + 1, hnext⟩ (by omega)
    have heven : (index.val + 1) % 2 = 0 := by omega
    simp only [angularIndex, ite_eq_left heven, ite_eq_right hodd]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self,
      Nat.cast_one, Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero]
    have hdiv : (index.val + 1) / 2 = index.val / 2 + 1 := by omega
    rw [hdiv, Nat.cast_add, Nat.cast_one]
    ring
  · rw [PositiveRoot.depth_layer, PositiveRoot.depth_layer, PositiveRoot.index_equiv,
      PositiveRoot.index_equiv]
    change (index.val + 1) / 2 + 1 = index.val / 2 + 1 + 1
    omega

/-- For odd n, the even root of the penultimate layer also ascends to the final root. -/
theorem depth_step_final {n : ℕ} (hthree : 3 ≤ n) (hodd : n % 2 = 1) :
    DepthStep hthree (positiveRootEquiv n ⟨n - 3, by omega⟩)
      (positiveRootEquiv n ⟨n - 1, by omega⟩) := by
  refine ⟨simpleRoot n hthree 1, Or.inr rfl, ?_, ?_⟩
  · apply simple_image hthree 1 ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩
      (by change n - 3 ≠ 1; omega)
    have hfirst : (n - 3) % 2 = 0 := by omega
    have hsecond : (n - 1) % 2 = 0 := by omega
    simp only [angularIndex, ite_eq_left hfirst, ite_eq_left hsecond,
      Fin.val_one, Nat.cast_one]
    have heq : (n - 1) / 2 + (n - 3) / 2 + 2 = n := by omega
    have hcast := congrArg (fun value : ℕ => (value : ZMod n)) heq
    simp only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self] at hcast
    linear_combination hcast
  · rw [PositiveRoot.depth_layer, PositiveRoot.depth_layer, PositiveRoot.index_equiv,
      PositiveRoot.index_equiv]
    change (n - 1) / 2 + 1 = (n - 3) / 2 + 1 + 1
    omega

private theorem simple_action_sum {n : ℕ} (hthree : 3 ≤ n) (simple : Fin 2)
    (index target : Fin n)
    (haction : realAction n (simpleRoot n hthree simple).reflection
      (positiveRoot n index) = positiveRoot n target) :
    (angularIndex index + angularIndex target + 2 * simple.val) % n = 0 := by
  let : NeZero n := ⟨by omega⟩
  have hc := PositiveRoot.signed_conjugation (simpleRoot n hthree simple).reflection
    (positiveRootEquiv n index) (positiveRootEquiv n target) (Or.inl haction)
  rw [simpleRoot_reflection, PositiveRoot.reflection_equiv,
    PositiveRoot.reflection_equiv, rootReflection_eq_sr_neg_angularIndex,
    rootReflection_eq_sr_neg_angularIndex] at hc
  symm at hc
  have hsum : ((angularIndex index + angularIndex target + 2 * simple.val : ℕ) :
      ZMod n) = 0 := by
    fin_cases simple
    · change DihedralGroup.sr 0 * DihedralGroup.sr (-(angularIndex index : ZMod n)) *
        (DihedralGroup.sr 0)⁻¹ = DihedralGroup.sr (-(angularIndex target : ZMod n)) at hc
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
        at hc
      have hcoord := DihedralGroup.sr.inj hc
      change ((angularIndex index + angularIndex target + 2 * 0 : ℕ) : ZMod n) = 0
      push_cast
      linear_combination hcoord
    · change DihedralGroup.sr 1 * DihedralGroup.sr (-(angularIndex index : ZMod n)) *
        (DihedralGroup.sr 1)⁻¹ = DihedralGroup.sr (-(angularIndex target : ZMod n)) at hc
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
        at hc
      have hcoord := DihedralGroup.sr.inj hc
      change ((angularIndex index + angularIndex target + 2 * 1 : ℕ) : ZMod n) = 0
      push_cast
      linear_combination hcoord
  rw [← ZMod.val_natCast, hsum, ZMod.val_zero]

private theorem zero_mod_small {n value : ℕ} (hpos : 0 < value) (hbound : value ≤ n)
    (hmod : value % n = 0) : value = n := by
  by_contra hne
  have hlt : value < n := by omega
  rw [Nat.mod_eq_of_lt hlt] at hmod
  omega

private theorem nonzero_mod_between {n value : ℕ} (hfirst : n < value)
    (hlast : value < 2 * n) : value % n ≠ 0 := by
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem step_indices {n : ℕ} (hthree : 3 ≤ n) (index target : Fin n)
    (hstep : DepthStep hthree (positiveRootEquiv n index) (positiveRootEquiv n target)) :
    (index.val % 2 = 0 ∧ target.val = index.val + 3) ∨
      (index.val % 2 ≠ 0 ∧ target.val = index.val + 1) ∨
      (n % 2 = 1 ∧ index.val = n - 3 ∧ target.val = n - 1) := by
  obtain ⟨alpha, hsimple, haction, hdepth⟩ := hstep
  obtain ⟨simple, rfl⟩ : ∃ simple : Fin 2, alpha = simpleRoot n hthree simple := by
    rcases hsimple with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have hmod := simple_action_sum hthree simple index target haction
  rw [PositiveRoot.depth_layer, PositiveRoot.depth_layer, PositiveRoot.index_equiv,
    PositiveRoot.index_equiv] at hdepth
  have hi := index.isLt
  have hj := target.isLt
  have hs := simple.isLt
  by_cases heven : index.val % 2 = 0
  · by_cases htarget : target.val % 2 = 0
    · have hjump : target.val = index.val + 2 := by omega
      have hsum : angularIndex index + angularIndex target + 2 * simple.val =
          index.val + 1 + 2 * simple.val := by
        simp only [angularIndex, ite_eq_left heven, ite_eq_left htarget]
        omega
      rw [hsum] at hmod
      have heq := zero_mod_small (by omega : 0 < index.val + 1 + 2 * simple.val)
        (by omega : index.val + 1 + 2 * simple.val ≤ n) hmod
      right; right
      omega
    · left
      exact ⟨heven, by omega⟩
  · by_cases htarget : target.val % 2 = 0
    · right; left
      exact ⟨heven, by omega⟩
    · have hjump : target.val = index.val + 2 := by omega
      have hsum : angularIndex index + angularIndex target + 2 * simple.val =
          2 * n - index.val - 2 + 2 * simple.val := by
        simp only [angularIndex, ite_eq_right heven, ite_eq_right htarget]
        omega
      rw [hsum] at hmod
      exact (nonzero_mod_between (by omega : n < 2 * n - index.val - 2 +
        2 * simple.val) (by omega : 2 * n - index.val - 2 + 2 * simple.val < 2 * n)
          hmod).elim

/-- The depth diagram consists of alternating chains and one final join for odd n. -/
theorem depth_step_iff {n : ℕ} (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) :
    DepthStep hthree alpha beta ↔
      (alpha.index.val % 2 = 0 ∧ beta.index.val = alpha.index.val + 3) ∨
      (alpha.index.val % 2 ≠ 0 ∧ beta.index.val = alpha.index.val + 1) ∨
      (n % 2 = 1 ∧ alpha.index.val = n - 3 ∧ beta.index.val = n - 1) := by
  obtain ⟨index, rfl⟩ := (positiveRootEquiv n).surjective alpha
  obtain ⟨target, rfl⟩ := (positiveRootEquiv n).surjective beta
  simp only [PositiveRoot.index_equiv]
  constructor
  · exact step_indices hthree index target
  · rintro (⟨heven, htarget⟩ | ⟨hodd, htarget⟩ | ⟨hodd, hindex, htarget⟩)
    · have heq : target = ⟨index.val + 3, by omega⟩ := Fin.ext htarget
      rw [heq]
      exact depth_step_even hthree index heven _
    · have heq : target = ⟨index.val + 1, by omega⟩ := Fin.ext htarget
      rw [heq]
      exact depth_step_odd hthree index hodd _
    · have heq : index = ⟨n - 3, by omega⟩ := Fin.ext hindex
      have hnext : target = ⟨n - 1, by omega⟩ := Fin.ext htarget
      rw [heq, hnext]
      exact depth_step_final hthree hodd

/-- Root-depth reachability is exactly reachability in the alternating-chain diagram. -/
theorem depth_order_iff {n : ℕ} (hthree : 3 ≤ n) (alpha beta : PositiveRoot n) :
    Relation.ReflTransGen (DepthStep hthree) alpha beta ↔
      Relation.ReflTransGen
        (fun first second : PositiveRoot n =>
          (first.index.val % 2 = 0 ∧ second.index.val = first.index.val + 3) ∨
          (first.index.val % 2 ≠ 0 ∧ second.index.val = first.index.val + 1) ∨
          (n % 2 = 1 ∧ first.index.val = n - 3 ∧ second.index.val = n - 1))
        alpha beta := by
  constructor
  · exact Relation.ReflTransGen.mono
      (fun first second => (depth_step_iff hthree first second).mp) alpha beta
  · exact Relation.ReflTransGen.mono
      (fun first second => (depth_step_iff hthree first second).mpr) alpha beta

end Schubert.Dihedral
