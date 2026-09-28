import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture


abbrev RiemannianMetric (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :=
  Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric


noncomputable def tangentNorm (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) : ℝ :=
  Real.sqrt (g.inner x v v)


noncomputable def pathELength (g : RiemannianMetric n M) (γ : ℝ → M)
    (a b : ℝ) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.pathELength (𝓡 n) γ a b


noncomputable def edist (g : RiemannianMetric n M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist (𝓡 n) x y


def ball (g : RiemannianMetric n M) (x : M) (r : ℝ) : Set M :=
  {y | g.edist x y < ENNReal.ofReal r}

end RiemannianMetric






structure LeviCivitaData (g : RiemannianMetric n M) where

  connection : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _)

  smooth : CovariantDerivative.ContMDiffCovariantDerivative connection ∞

  torsion_eq_zero : connection.torsion = 0

  metricCompatible :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    connection.IsMetricCompatible

end PoincareConjecture
