import Schubert.Dihedral.CyclicWindow
import Schubert.Dihedral.CyclicSourceWindow
import Schubert.Dihedral.CyclicWindowSources
import Schubert.Dihedral.CyclicTranslation
import Schubert.DihedralSplines.CyclicWindowEdges

/-! # Separation witnesses for finite cyclic intervals -/

namespace Schubert.Dihedral.Cyclic

private theorem normalized_separation {n : ℕ} {hthree : 3 ≤ n}
    (selected : RootSubset n) (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      length n hthree alpha.reflection ≤ 2 * half + 1 → alpha.val ∈ selected)
    (active : Set (Fin (2 * n)))
    (hactive : (⟨0, by omega⟩ : Fin (2 * n)) ∈ active ∨ ⟨1, by omega⟩ ∈ active) :
    ∃ chosen ∈ active, ∃ source ∈ interval n hthree chosen (2 * half + 2),
      (∀ other ∈ active, other ≠ chosen →
        source ∉ interval n hthree other (2 * half + 2)) ∨
      ∃ alpha : PositiveRoot n, alpha.val ∈ selected ∧
        source * alpha.reflection ∈ interval n hthree chosen (2 * half + 2) ∧
        ∀ other ∈ active, other ≠ chosen →
          source ∈ interval n hthree other (2 * half + 2) →
          source * alpha.reflection ∉ interval n hthree other (2 * half + 2) := by
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  let size := 2 * half + 2
  let base : Fin (2 * n) := ⟨2 * n - size + 1, by dsimp [size]; omega⟩
  let index (j : ℕ) : Fin (2 * n) := ⟨(base.val + j) % (2 * n), Nat.mod_lt _ (by omega)⟩
  have hsize : size ≤ n := by dsimp [size]; omega
  have hindex (j : ℕ) (hj : j ≤ size) : index j = base + ⟨j, by omega⟩ := rfl
  have hzero : index (size - 1) = ⟨0, by omega⟩ := by
    dsimp only [index, base]
    apply Fin.ext
    dsimp only [Fin.val_mk]
    have heq : 2 * n - size + 1 + (size - 1) = 2 * n := by dsimp [size]; omega
    rw [heq, Nat.mod_self]
  have hone : index size = ⟨1, by omega⟩ := by
    dsimp only [index, base]
    apply Fin.ext
    dsimp only [Fin.val_mk]
    have heq : 2 * n - size + 1 + size = 2 * n + 1 := by dsimp [size]; omega
    rw [heq]
    simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (show 1 < 2 * n by omega)
  have hexists : ∃ j, j ≤ size ∧ index j ∈ active := by
    rcases hactive with hz | ho
    · exact ⟨size - 1, by omega, hzero ▸ hz⟩
    · exact ⟨size, le_rfl, hone ▸ ho⟩
  let first := Nat.find hexists
  have hfirst : first ≤ size ∧ index first ∈ active := Nat.find_spec hexists
  have hminimum (j : ℕ) (hj : j ≤ size) (ha : index j ∈ active) : first ≤ j :=
    Nat.find_min' hexists ⟨hj, ha⟩
  have hwindow (other : Fin (2 * n))
      (hsource : vertex n hthree ⟨0, by omega⟩ ∈ interval n hthree other size ∨
        vertex n hthree ⟨1, by omega⟩ ∈ interval n hthree other size) :
      ∃ j, j ≤ size ∧ other = index j := by
    have hw := (source_window size (by dsimp [size]; omega) hsize other).mp hsource
    rcases hw with hsmall | htail
    · refine ⟨size - 1 + other.val, by dsimp [size]; omega, ?_⟩
      apply Fin.ext
      dsimp only [index, base, Fin.val_mk]
      have heq : 2 * n - size + 1 + (size - 1 + other.val) = 2 * n + other.val := by
        dsimp [size]; omega
      rw [heq]
      simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      exact (Nat.mod_eq_of_lt other.isLt).symm
    · refine ⟨other.val - base.val, ?_, ?_⟩
      · dsimp [base] at *; omega
      · apply Fin.ext
        dsimp only [index, Fin.val_mk]
        have heq : base.val + (other.val - base.val) = other.val := by
          dsimp [base] at *; omega
        rw [heq, Nat.mod_eq_of_lt other.isLt]
  have hexcludes (other : Fin (2 * n)) (ha : other ∈ active) (hne : other ≠ index first)
      (hsource : vertex n hthree ⟨0, by omega⟩ ∈ interval n hthree other size ∨
        vertex n hthree ⟨1, by omega⟩ ∈ interval n hthree other size) :
      vertex n hthree (index first) ∉ interval n hthree other size := by
    obtain ⟨j, hj, hother⟩ := hwindow other hsource
    have hle := hminimum j hj (hother ▸ ha)
    have hlt : first < j := by
      have hneq : first ≠ j := by intro heq; exact hne (hother.trans (congrArg index heq).symm)
      omega
    rw [hother, hindex first hfirst.1, hindex j hj]
    exact excludes_earlier base size hsize first j hlt hj
  have hstart : vertex n hthree (index first) ∈ interval n hthree (index first) size := by
    rw [mem_interval _ _ _ (by omega), sub_self]
    dsimp [size]; omega
  have hvertex_zero : vertex n hthree ⟨0, by omega⟩ = 1 := by
    rw [vertex, PositiveRoot.alternating_zero]
  have hvertex_one : vertex n hthree ⟨1, by omega⟩ = (simpleRoot n hthree 0).reflection := by
    rw [vertex, PositiveRoot.alternating_succ, PositiveRoot.alternating_zero, mul_one]
  by_cases hterminal : size - 1 ≤ first
  · refine ⟨index first, hfirst.2, vertex n hthree (index first), hstart, Or.inl ?_⟩
    intro other ha hne hmem
    apply hexcludes other ha hne ?_ hmem
    have hcases : first = size - 1 ∨ first = size := by omega
    rcases hcases with hz | ho
    · exact Or.inl (by simpa only [hz, hzero] using hmem)
    · exact Or.inr (by simpa only [ho, hone] using hmem)
  · have hfirst_lt : first < size - 1 := by omega
    by_cases heven : Even first
    · obtain ⟨r, hr⟩ := heven
      have htail : index first = ⟨2 * n - (2 * (half - r) + 1), by omega⟩ := by
        apply Fin.ext
        dsimp only [index, base, Fin.val_mk]
        have heq : 2 * n - size + 1 + first = 2 * n - (2 * (half - r) + 1) := by
          dsimp [size] at *; omega
        rw [heq, Nat.mod_eq_of_lt (by dsimp [size] at *; omega)]
      have hedge := selected.tail_odd_edge half hbound hselected (half - r) (by omega)
      obtain ⟨alpha, halpha, htarget⟩ := selected.mem_edges _ |>.mp hedge
      change vertex n hthree ⟨2 * n - (2 * (half - r) + 1), by omega⟩ =
        1 * alpha.reflection at htarget
      refine ⟨index first, hfirst.2, 1, ?_, Or.inr ⟨alpha, halpha, ?_, ?_⟩⟩
      · rw [htail]; exact zero_in_odd_interval half (half - r) hbound (by omega)
      · rw [← htarget, ← htail]; exact hstart
      · intro other ha hne hmem
        rw [← htarget, ← htail]
        exact hexcludes other ha hne (Or.inl (hvertex_zero.symm ▸ hmem))
    · have hodd : Odd first := Nat.not_even_iff_odd.mp heven
      obtain ⟨r, hr⟩ := hodd
      have htail : index first = ⟨2 * n - 2 * (half - r), by omega⟩ := by
        apply Fin.ext
        dsimp only [index, base, Fin.val_mk]
        have heq : 2 * n - size + 1 + first = 2 * n - 2 * (half - r) := by
          dsimp [size] at *; omega
        rw [heq, Nat.mod_eq_of_lt (by dsimp [size] at *; omega)]
      have hoffset : 0 < half - r := by dsimp [size] at *; omega
      have hedge := selected.tail_even_edge half hbound hselected (half - r) hoffset (by omega)
      obtain ⟨alpha, halpha, htarget⟩ := selected.mem_edges _ |>.mp hedge
      change vertex n hthree ⟨2 * n - 2 * (half - r), by omega⟩ =
        (simpleRoot n hthree 0).reflection * alpha.reflection at htarget
      refine ⟨index first, hfirst.2, (simpleRoot n hthree 0).reflection, ?_,
        Or.inr ⟨alpha, halpha, ?_, ?_⟩⟩
      · rw [htail]; exact one_in_even_interval half (half - r) hbound hoffset (by omega)
      · rw [← htarget, ← htail]; exact hstart
      · intro other ha hne hmem
        rw [← htarget, ← htail]
        exact hexcludes other ha hne (Or.inr (hvertex_one.symm ▸ hmem))

private theorem translated_mem {n : ℕ} {hthree : 3 ≤ n}
    (origin start : Fin (2 * n)) (heven : Even origin.val) (size : ℕ)
    (source : DihedralGroup n) :
    vertex n hthree origin * source ∈ interval n hthree (origin + start) size ↔
      source ∈ interval n hthree start size := by
  classical
  rw [← interval_translate origin start heven size, Finset.mem_image]
  constructor
  · rintro ⟨previous, hprevious, heq⟩
    have hsame := mul_left_cancel heq
    exact hsame ▸ hprevious
  · intro hsource
    exact ⟨source, hsource, rfl⟩

/-- Every nonempty family of short intervals has an isolated source or an internal selected
reflection whose target is excluded by every other interval meeting the source. -/
theorem separation {n : ℕ} {hthree : 3 ≤ n}
    (selected : RootSubset n) (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      length n hthree alpha.reflection ≤ 2 * half + 1 → alpha.val ∈ selected)
    (active : Set (Fin (2 * n))) (hnonempty : active.Nonempty) :
    ∃ chosen ∈ active, ∃ source ∈ interval n hthree chosen (2 * half + 2),
      (∀ other ∈ active, other ≠ chosen →
        source ∉ interval n hthree other (2 * half + 2)) ∨
      ∃ alpha : PositiveRoot n, alpha.val ∈ selected ∧
        source * alpha.reflection ∈ interval n hthree chosen (2 * half + 2) ∧
        ∀ other ∈ active, other ≠ chosen →
          source ∈ interval n hthree other (2 * half + 2) →
          source * alpha.reflection ∉ interval n hthree other (2 * half + 2) := by
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨initial, hinitial⟩ := hnonempty
  let origin : Fin (2 * n) := ⟨2 * (initial.val / 2), by omega⟩
  have heven : Even origin.val := ⟨initial.val / 2, by dsimp [origin]; omega⟩
  let shifted : Set (Fin (2 * n)) := {position | origin + position ∈ active}
  have hactive : (⟨0, by omega⟩ : Fin (2 * n)) ∈ shifted ∨ ⟨1, by omega⟩ ∈ shifted := by
    have hremainder : initial.val % 2 = 0 ∨ initial.val % 2 = 1 := by omega
    rcases hremainder with hz | ho
    · left
      change origin + ⟨0, by omega⟩ ∈ active
      have heq : origin + ⟨0, by omega⟩ = initial := by
        apply Fin.ext
        change (2 * (initial.val / 2) + 0) % (2 * n) = initial.val
        have hval : 2 * (initial.val / 2) + 0 = initial.val := by omega
        rw [hval, Nat.mod_eq_of_lt initial.isLt]
      exact heq ▸ hinitial
    · right
      change origin + ⟨1, by omega⟩ ∈ active
      have heq : origin + ⟨1, by omega⟩ = initial := by
        apply Fin.ext
        change (2 * (initial.val / 2) + 1) % (2 * n) = initial.val
        have hval : 2 * (initial.val / 2) + 1 = initial.val := by omega
        rw [hval, Nat.mod_eq_of_lt initial.isLt]
      exact heq ▸ hinitial
  obtain ⟨chosen, hchosen, source, hsource, hisolated | hinternal⟩ :=
    normalized_separation selected half hbound hselected shifted hactive
  · refine ⟨origin + chosen, hchosen, vertex n hthree origin * source,
      (translated_mem origin chosen heven _ source).mpr hsource, Or.inl ?_⟩
    intro other hother hne hmem
    have hshifted : other - origin ∈ shifted := by
      change origin + (other - origin) ∈ active
      simpa only [add_sub_cancel] using hother
    have hdistinct : other - origin ≠ chosen := by
      intro heq
      apply hne
      rw [← heq, add_sub_cancel]
    have hrewrite : origin + (other - origin) = other := add_sub_cancel _ _
    exact hisolated (other - origin) hshifted hdistinct
      ((translated_mem origin (other - origin) heven _ source).mp (hrewrite.symm ▸ hmem))
  · obtain ⟨alpha, halpha, htarget, hexcludes⟩ := hinternal
    refine ⟨origin + chosen, hchosen, vertex n hthree origin * source,
      (translated_mem origin chosen heven _ source).mpr hsource,
      Or.inr ⟨alpha, halpha, ?_, ?_⟩⟩
    · rw [mul_assoc]
      exact (translated_mem origin chosen heven _ _).mpr htarget
    · intro other hother hne hmem htarget_mem
      have hshifted : other - origin ∈ shifted := by
        change origin + (other - origin) ∈ active
        simpa only [add_sub_cancel] using hother
      have hdistinct : other - origin ≠ chosen := by
        intro heq
        apply hne
        rw [← heq, add_sub_cancel]
      have hrewrite : origin + (other - origin) = other := add_sub_cancel _ _
      apply hexcludes (other - origin) hshifted hdistinct
        ((translated_mem origin (other - origin) heven _ source).mp (hrewrite.symm ▸ hmem))
      rw [mul_assoc] at htarget_mem
      exact (translated_mem origin (other - origin) heven _ _).mp
        (hrewrite.symm ▸ htarget_mem)

end Schubert.Dihedral.Cyclic
