import PoincareConjecture.Definitions.M60Area

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

noncomputable def m60RoundSphereInner (p : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) p) : ℝ :=
  inner ℝ
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) p v)
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) p w)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def M60WeaklyConformal (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : Prop :=
  ∀ p : UnitTwoSphere, ∃ scale : ℝ, 0 ≤ scale ∧
    ∀ v w : TangentSpace (𝓡 2) p,
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
        (mfderiv (𝓡 2) (𝓡 n) f p w) = scale * m60RoundSphereInner p v w

def M60EnergyStationary (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ variation : ℝ × UnitTwoSphere → M,
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ variation
        (Set.Ioo (-epsilon) epsilon ×ˢ (Set.univ : Set UnitTwoSphere)) →
      (∀ p : UnitTwoSphere, variation (0, p) = f p) →
      HasDerivAt
        (fun s : ℝ => m60SphereEnergy g (fun p => variation (s, p))) 0 0

def m60SphereBranchSet (f : UnitTwoSphere → M) : Set UnitTwoSphere :=
  {p | mfderiv (𝓡 2) (𝓡 n) f p = 0}

structure M60BranchedMinimalSphere (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : Prop where
  smooth : ContMDiff (𝓡 2) (𝓡 n) ∞ f
  nonconstant : ∃ p q : UnitTwoSphere, f p ≠ f q
  weakly_conformal : M60WeaklyConformal g f
  energy_stationary : M60EnergyStationary g f
  finite_branch_set : (m60SphereBranchSet (n := n) f).Finite
  injective_off_branch_set : ∀ p : UnitTwoSphere,
    p ∉ m60SphereBranchSet (n := n) f →
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) f p)

end PoincareConjecture
