import Schubert.Dihedral.HyperplanePullback

/-! # Unique extremal pairs for arbitrary generic root hyperplanes -/

namespace Schubert.Dihedral.Separator

/-- Every generic hyperplane has a unique pair of nearest positive unit roots. -/
theorem unique_closest_pair {n : ℕ} (data : Separator n) (hthree : 3 ≤ n) :
    ∃! pair : Finset RealPlane, pair.card = 2 ∧ (↑pair : Set RealPlane) ⊆ data.positive ∧
      ∀ first ∈ pair, ∀ second ∈ data.positive, second ∉ pair →
        realBilinearForm first data.normal < realBilinearForm second data.normal := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨element, himage⟩ := data.exists_chamber hthree
  let pulled := data.pullback element
  let e : RealPlane ≃ RealPlane := (realLinearEquiv n element).toEquiv
  let E := e.finsetCongr
  have hpositive := data.positive_pullback element himage
  have hpos (vector : RealPlane) : vector ∈ pulled.positive ↔ e vector ∈ data.positive := by
    rw [hpositive, himage]
    constructor
    · intro hvector
      exact ⟨vector, hvector, rfl⟩
    · rintro ⟨root, hroot, heq⟩
      exact e.injective heq ▸ hroot
  have hmem (pair : Finset RealPlane) (vector : RealPlane) :
      e vector ∈ E pair ↔ vector ∈ pair := by
    simp [E]
  have hpairing (vector : RealPlane) : realBilinearForm vector pulled.normal =
      realBilinearForm (e vector) data.normal := data.transpose_pairing element vector
  let P := fun (separator : Separator n) (pair : Finset RealPlane) =>
    pair.card = 2 ∧ (↑pair : Set RealPlane) ⊆ separator.positive ∧
      ∀ first ∈ pair, ∀ second ∈ separator.positive, second ∉ pair →
        realBilinearForm first separator.normal < realBilinearForm second separator.normal
  have htransport (pair : Finset RealPlane) : P pulled pair ↔ P data (E pair) := by
    constructor
    · rintro ⟨hcard, hsubset, hclosest⟩
      refine ⟨by simpa [E] using hcard, ?_, ?_⟩
      · intro vector hvector
        obtain ⟨root, hroot, rfl⟩ := Finset.mem_map.mp hvector
        exact (hpos root).mp (hsubset hroot)
      · intro first hfirst second hsecond hout
        obtain ⟨root, hroot, rfl⟩ := Finset.mem_map.mp hfirst
        obtain ⟨other, rfl⟩ := e.surjective second
        have hlt := hclosest root hroot other ((hpos other).mpr hsecond)
          (fun hother => hout ((hmem pair other).mpr hother))
        change realBilinearForm (e root) data.normal <
          realBilinearForm (e other) data.normal
        simpa only [hpairing] using hlt
    · rintro ⟨hcard, hsubset, hclosest⟩
      refine ⟨by simpa [E] using hcard, ?_, ?_⟩
      · intro vector hvector
        exact (hpos vector).mpr (hsubset ((hmem pair vector).mpr hvector))
      · intro first hfirst second hsecond hout
        have hlt := hclosest (e first) ((hmem pair first).mpr hfirst)
          (e second) ((hpos second).mp hsecond)
          (fun hother => hout ((hmem pair second).mp hother))
        simpa only [hpairing] using hlt
  exact (E.existsUnique_congr htransport).mp (pulled.closest_pair hthree hpositive)

end Schubert.Dihedral.Separator
