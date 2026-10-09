import DihedralHessenberg.Paper.CyclicSeparation
import DihedralHessenberg.Dihedral.CyclicBlockForms

/-! # Reflection separation of alternating block families -/

namespace Schubert.Dihedral.RootSubset

/-- A nonempty family of short alternating blocks has an isolated vertex or a selected
internal reflection target excluded by every other block meeting that vertex. -/
theorem block_separation {n : ℕ} {hthree : 3 ≤ n}
    (selected : RootSubset n) (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      Schubert.Dihedral.length n hthree alpha.reflection ≤ 2 * half + 1 →
        alpha.val ∈ selected)
    (family : Set (Finset (DihedralGroup n))) (hnonempty : family.Nonempty)
    (hblocks : ∀ block ∈ family,
      (∃ base, block = alternatingBlock base (simpleRoot n hthree 0)
        (simpleRoot n hthree 1) half) ∨
      (∃ base, block = alternatingBlock base (simpleRoot n hthree 1)
        (simpleRoot n hthree 0) half)) :
    ∃ chosen ∈ family, ∃ source ∈ chosen,
      (∀ other ∈ family, other ≠ chosen → source ∉ other) ∨
      ∃ alpha : PositiveRoot n, alpha.val ∈ selected ∧ source * alpha.reflection ∈ chosen ∧
        ∀ other ∈ family, other ≠ chosen → source ∈ other →
          source * alpha.reflection ∉ other := by
  classical
  have hinterval (block : Finset (DihedralGroup n)) (hblock : block ∈ family) :
      ∃ start, block = Cyclic.interval n hthree start (2 * half + 2) := by
    rcases hblocks block hblock with ⟨base, hfirst⟩ | ⟨base, hsecond⟩
    · obtain ⟨start, _, hstart⟩ := Cyclic.first_interval (hthree := hthree) base half hbound
      exact ⟨start, hfirst.trans hstart⟩
    · obtain ⟨start, _, hstart⟩ := Cyclic.second_interval (hthree := hthree) base half hbound
      exact ⟨start, hsecond.trans hstart⟩
  let active : Set (Fin (2 * n)) :=
    {start | Cyclic.interval n hthree start (2 * half + 2) ∈ family}
  have ha : active.Nonempty := by
    obtain ⟨block, hblock⟩ := hnonempty
    obtain ⟨start, hstart⟩ := hinterval block hblock
    exact ⟨start, show Cyclic.interval n hthree start (2 * half + 2) ∈ family from
      hstart ▸ hblock⟩
  obtain ⟨chosen, hchosen, source, hsource, hisolated | hinternal⟩ :=
    Cyclic.separation selected half hbound hselected active ha
  · refine ⟨Cyclic.interval n hthree chosen (2 * half + 2), hchosen,
      source, hsource, Or.inl ?_⟩
    intro other hother hne hmem
    obtain ⟨start, hstart⟩ := hinterval other hother
    have hdistinct : start ≠ chosen := by intro heq; exact hne (hstart.trans (heq ▸ rfl))
    exact hisolated start
      (show Cyclic.interval n hthree start (2 * half + 2) ∈ family from hstart ▸ hother)
      hdistinct (hstart ▸ hmem)
  · obtain ⟨alpha, halpha, htarget, hexcludes⟩ := hinternal
    refine ⟨Cyclic.interval n hthree chosen (2 * half + 2), hchosen,
      source, hsource, Or.inr ⟨alpha, halpha, htarget, ?_⟩⟩
    intro other hother hne hmem htarget_mem
    obtain ⟨start, hstart⟩ := hinterval other hother
    have hdistinct : start ≠ chosen := by intro heq; exact hne (hstart.trans (heq ▸ rfl))
    exact hexcludes start
      (show Cyclic.interval n hthree start (2 * half + 2) ∈ family from hstart ▸ hother)
      hdistinct (hstart ▸ hmem) (hstart ▸ htarget_mem)

end Schubert.Dihedral.RootSubset
