import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.SphereArea

/-!
# M60 primitive branched-minimal sphere properties

The specified sphere map is smooth, nonconstant, weakly conformal and
stationary for its actual Dirichlet energy. Its branch set is the actual
zero set of its differential, with immersion away from that finite set.
No Gauss-Bonnet inequality or positive pullback metric at branch points is
included as a premise.

Source: Morgan--Tian Lemma 18.10 and Claim 18.12, printed pp. 424-427;
Sacks--Uhlenbeck, Theorem 1.6, printed p. 5, with its branch convention on
printed p. 1. See `reviews/contracts/M60-round1.md` and
`reviews/errata/2026-09-14-sphere-area.md` for normalization and source checks.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- The standard round inner product, pulled back by the actual sphere
inclusion into Euclidean three-space. -/
noncomputable def m60RoundSphereInner (p : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) p) : ℝ :=
  inner ℝ
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) p v)
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) p w)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual pullback metric is a nonnegative multiple of the round metric;
the multiple is allowed to vanish at a branch point. -/
def M60WeaklyConformal (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : Prop :=
  ∀ p : UnitTwoSphere, ∃ scale : ℝ, 0 ≤ scale ∧
    ∀ v w : TangentSpace (𝓡 2) p,
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
        (mfderiv (𝓡 2) (𝓡 n) f p w) = scale * m60RoundSphereInner p v w

/-- Harmonicity as stationarity under every smooth local sphere variation.
The derivative assertion includes existence and fixes the target metric. -/
def M60EnergyStationary (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ variation : ℝ × UnitTwoSphere → M,
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ variation
        (Set.Ioo (-epsilon) epsilon ×ˢ (Set.univ : Set UnitTwoSphere)) →
      (∀ p : UnitTwoSphere, variation (0, p) = f p) →
      HasDerivAt
        (fun s : ℝ => m60SphereEnergy g (fun p => variation (s, p))) 0 0

/-- The actual differential-zero set, independent of any proposed branch
certificate or any chosen finite superset. -/
def m60SphereBranchSet (f : UnitTwoSphere → M) : Set UnitTwoSphere :=
  {p | mfderiv (𝓡 2) (𝓡 n) f p = 0}

/-- A nonconstant branched minimal sphere stated entirely as primitive
properties of its displayed smooth map and the fixed metric. -/
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

end PoincareMT
