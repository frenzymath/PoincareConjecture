import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch01/RiemannianMetric.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Explicit Riemannian metric and connection data

The chosen metric is an argument of each operation, including extended distance.
This follows Morgan-Tian, printed pp. 3-4, using Mathlib's tangent bundle and
connection conventions. The distance uses C^1 paths; transport to the book's
smooth-path convention is a separate obligation. See reviews/contracts/metric-v1.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

/-- A smooth positive-definite symmetric metric on a manifold without boundary. -/
abbrev RiemannianMetric (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :=
  Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric

/-- The norm of a tangent vector in the explicitly chosen metric. -/
noncomputable def tangentNorm (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) : ℝ :=
  Real.sqrt (g.inner x v v)

/-- The derivative-integral functional; geometric length requires a regular path. -/
noncomputable def pathELength (g : RiemannianMetric n M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.pathELength (𝓡 n) γ a b

/-- The infimum of C^1 path lengths, retaining infinity between path components. -/
noncomputable def edist (g : RiemannianMetric n M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist (𝓡 n) x y

/-- An open metric ball, with the empty set as its value for nonpositive radii. -/
def ball (g : RiemannianMetric n M) (x : M) (r : ℝ) : Set M :=
  {y | g.edist x y < ENNReal.ofReal r}

end RiemannianMetric

end PoincareMT
