import DihedralHessenberg.Dihedral.RootLatticeAxioms
import DihedralHessenberg.Dihedral.A2Roots
import DihedralHessenberg.Dihedral.C2Roots
import DihedralHessenberg.Dihedral.G2Integral
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Finite reduced crystallographic root configurations in the real plane -/

namespace Schubert.Dihedral.RootLattice

/-- The Euclidean finite, spanning, reduced, reflection-closed, integral root-system axioms. -/
structure Crystallographic (lattice : RootLattice) : Prop where
  /-- There are finitely many signed roots. -/
  finite : lattice.roots.Finite
  /-- The signed roots span the real plane. -/
  span : Submodule.span ℝ lattice.roots = ⊤
  /-- Every signed root is nonzero, expressed by its positive square norm. -/
  norm_pos : ∀ vector ∈ lattice.roots, 0 < realBilinearForm vector vector
  /-- The only roots proportional to a root are it and its negative. -/
  reduced : ∀ first ∈ lattice.roots, ∀ second ∈ lattice.roots, ∀ scalar : ℝ,
    first = scalar • second → scalar = 1 ∨ scalar = -1
  /-- Reflection in every signed root preserves all signed roots. -/
  reflection_mem : ∀ normal ∈ lattice.roots, ∀ vector ∈ lattice.roots,
    vector - (2 * realBilinearForm vector normal /
      realBilinearForm normal normal) • normal ∈ lattice.roots
  /-- Root-coroot pairings are integers. -/
  integral : ∀ normal ∈ lattice.roots, ∀ vector ∈ lattice.roots,
    ∃ integer : ℤ, 2 * realBilinearForm vector normal /
      realBilinearForm normal normal = (integer : ℝ)

private theorem simple_span (lattice : RootLattice)
    (hindependent : LinearIndependent ℝ ![lattice.first, lattice.second])
    (hfirst : lattice.first ∈ lattice.positive) (hsecond : lattice.second ∈ lattice.positive) :
    Submodule.span ℝ lattice.roots = ⊤ := by
  have hspan := hindependent.span_eq_top_of_card_eq_finrank (by
    simp [RealPlane])
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro vector ⟨index, rfl⟩
  fin_cases index
  · exact Or.inl hfirst
  · exact Or.inl hsecond

/-- The A configuration satisfies every reduced crystallographic root-system axiom. -/
theorem a2_crystallographic : a2.Crystallographic where
  finite := a2Rescaling.roots_finite
  span := simple_span a2 a2_independent (by simp [a2]) (by simp [a2])
  norm_pos := a2Rescaling.norm_pos
  reduced := fun first hfirst second hsecond scalar heq =>
    a2Rescaling.reduced first second hfirst hsecond scalar heq
  reflection_mem := fun normal hnormal vector hvector =>
    a2Rescaling.reflection_mem normal vector hnormal hvector
  integral := fun normal hnormal vector hvector => a2_integral normal vector hnormal hvector

/-- The B configuration satisfies every reduced crystallographic root-system axiom. -/
theorem b2_crystallographic : b2.Crystallographic where
  finite := b2Rescaling.roots_finite
  span := simple_span b2 b2_independent (by simp [b2]) (by simp [b2])
  norm_pos := b2Rescaling.norm_pos
  reduced := fun first hfirst second hsecond scalar heq =>
    b2Rescaling.reduced first second hfirst hsecond scalar heq
  reflection_mem := fun normal hnormal vector hvector =>
    b2Rescaling.reflection_mem normal vector hnormal hvector
  integral := fun normal hnormal vector hvector => b2_integral normal vector hnormal hvector

/-- The C configuration satisfies every reduced crystallographic root-system axiom. -/
theorem c2_crystallographic : c2.Crystallographic where
  finite := c2Rescaling.roots_finite
  span := simple_span c2 c2_independent (by simp [c2]) (by simp [c2])
  norm_pos := c2Rescaling.norm_pos
  reduced := fun first hfirst second hsecond scalar heq =>
    c2Rescaling.reduced first second hfirst hsecond scalar heq
  reflection_mem := fun normal hnormal vector hvector =>
    c2Rescaling.reflection_mem normal vector hnormal hvector
  integral := fun normal hnormal vector hvector => c2_integral normal vector hnormal hvector

/-- The G configuration satisfies every reduced crystallographic root-system axiom. -/
theorem g2_crystallographic : g2.Crystallographic where
  finite := g2Rescaling.roots_finite
  span := simple_span g2 g2_independent (by simp [g2]) (by simp [g2])
  norm_pos := g2Rescaling.norm_pos
  reduced := fun first hfirst second hsecond scalar heq =>
    g2Rescaling.reduced first second hfirst hsecond scalar heq
  reflection_mem := fun normal hnormal vector hvector =>
    g2Rescaling.reflection_mem normal vector hnormal hvector
  integral := fun normal hnormal vector hvector => g2_integral normal vector hnormal hvector

end Schubert.Dihedral.RootLattice
