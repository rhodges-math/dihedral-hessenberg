import Schubert.Dihedral.CrystallographicNumbering

/-! # Positive-vector bijections for radial root configurations -/

noncomputable section

namespace Schubert.Dihedral.RootLattice

/-- An arbitrary subset of positive lattice vectors closed under integer root comparison. -/
def Lower (lattice : RootLattice) (selected : Set RealPlane) : Prop :=
  selected ⊆ lattice.positive ∧
    ∀ alpha beta : RealPlane, alpha ∈ lattice.positive → beta ∈ lattice.positive →
      lattice.LE alpha beta → beta ∈ selected → alpha ∈ selected

/-- A positive conjugacy-invariant radial realization of the positive unit-root carrier. -/
structure Rescaling (lattice : RootLattice) (n : ℕ) where
  /-- The positive radius on each unit direction. -/
  radius : PositiveRoot n → ℝ
  /-- No radius vanishes or reverses its direction. -/
  positive : ∀ alpha, 0 < radius alpha
  /-- The radial vectors are exactly the specified positive configuration. -/
  carrier : lattice.positive = Set.range (fun alpha => radius alpha • alpha.val)
  /-- Reflection-conjugate directions have the same radius. -/
  conjugate : ∀ alpha beta, IsConj alpha.reflection beta.reflection → radius alpha = radius beta

namespace Rescaling

variable {lattice : RootLattice} {n : ℕ}

/-- The scaled positive-vector map is injective. -/
theorem injective (data : Rescaling lattice n) :
    Function.Injective (fun alpha : PositiveRoot n => data.radius alpha • alpha.val) :=
  PositiveRoot.scaled_injective data.radius data.positive

/-- Positive unit vectors are in bijection with positive radial vectors. -/
def equiv (data : Rescaling lattice n) : PositiveRoot n ≃ {vector // vector ∈ lattice.positive} :=
  Equiv.ofBijective (fun alpha =>
    ⟨data.radius alpha • alpha.val, data.carrier.symm ▸ ⟨alpha, rfl⟩⟩) (by
      constructor
      · intro alpha beta heq
        exact data.injective (congrArg Subtype.val heq)
      · intro vector
        have hmem := Eq.mp
          (congrArg (fun carrier : Set RealPlane => vector.val ∈ carrier) data.carrier)
          vector.property
        obtain ⟨alpha, heq⟩ := hmem
        exact ⟨alpha, Subtype.ext heq⟩)

/-- A subset of unit-root vectors has its radial image. -/
def image (data : Rescaling lattice n) (selected : Set RealPlane) : Set RealPlane :=
  (fun alpha : PositiveRoot n => data.radius alpha • alpha.val) '' {alpha | alpha.val ∈ selected}

/-- The radial image preserves membership of each positive direction. -/
theorem mem_image (data : Rescaling lattice n) (selected : Set RealPlane)
    (alpha : PositiveRoot n) :
    data.radius alpha • alpha.val ∈ data.image selected ↔ alpha.val ∈ selected := by
  constructor
  · rintro ⟨beta, hbeta, heq⟩
    have hequal := data.injective heq
    exact hequal ▸ hbeta
  · intro hmem
    exact ⟨alpha, hmem, rfl⟩

/-- Every subset image lies in the positive radial carrier. -/
theorem image_subset (data : Rescaling lattice n) (selected : Set RealPlane) :
    data.image selected ⊆ lattice.positive := by
  rintro vector ⟨alpha, _, rfl⟩
  rw [data.carrier]
  exact ⟨alpha, rfl⟩

/-- The positive radial carrier is finite. -/
theorem finite (data : Rescaling lattice n) : lattice.positive.Finite := by
  rw [data.carrier]
  exact Set.finite_range _

/-- The radial normal defines the group reflection. -/
theorem reflection (data : Rescaling lattice n) (alpha : PositiveRoot n) (vector : RealPlane) :
    vector - (2 * realBilinearForm vector (data.radius alpha • alpha.val) /
      realBilinearForm (data.radius alpha • alpha.val) (data.radius alpha • alpha.val)) •
      (data.radius alpha • alpha.val) = realAction n alpha.reflection vector :=
  PositiveRoot.scaled_reflection alpha _ (ne_of_gt (data.positive alpha)) vector

end Rescaling

/-- The B configuration is the intrinsic short/long class rescaling of four unit directions. -/
def b2Rescaling : Rescaling b2 4 where
  radius := PositiveRoot.classRadius (by decide) 1 (Real.sqrt 2)
  positive := PositiveRoot.classRadius_pos _ _ (by norm_num) (by positivity)
  carrier := b2_image
  conjugate := PositiveRoot.classRadius_conj _ _

/-- The C configuration uses the opposite short/long class assignment. -/
def c2Rescaling : Rescaling c2 4 where
  radius := PositiveRoot.classRadius (by decide) (Real.sqrt 2) 1
  positive := PositiveRoot.classRadius_pos _ _ (by positivity) (by norm_num)
  carrier := c2_image
  conjugate := PositiveRoot.classRadius_conj _ _

/-- The G configuration has long-to-short squared length ratio three. -/
def g2Rescaling : Rescaling g2 6 where
  radius := PositiveRoot.classRadius (by decide) 1 (Real.sqrt 3)
  positive := PositiveRoot.classRadius_pos _ _ (by norm_num) (by positivity)
  carrier := g2_image
  conjugate := PositiveRoot.classRadius_conj _ _

end Schubert.Dihedral.RootLattice
