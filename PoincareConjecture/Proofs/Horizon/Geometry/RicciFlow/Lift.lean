import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe v u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}

local instance uliftChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} M) :=
  Poincare.Manifold.uliftChartedSpace _ M

local instance uliftIsManifold : IsManifold (𝓡 n) ∞ (ULift.{v} M) :=
  Poincare.Manifold.uliftIsManifold (𝓡 n) M

noncomputable def ulift (F : RicciFlow n M J) : RicciFlow n (ULift.{v} M) J :=
  F.pullbackDiffeomorph (Poincare.Manifold.uliftDiffeomorph (𝓡 n) M)

@[simp] theorem ulift_scalarCurvature (F : RicciFlow n M J)
    (t : ℝ) (x : ULift.{v} M) :
    (F.ulift.connection t).scalarCurvature x = (F.connection t).scalarCurvature x.down :=
  F.pullbackDiffeomorph_scalarCurvature _ t x

@[simp] theorem ulift_curvatureTensorNorm (F : RicciFlow n M J)
    (t : ℝ) (x : ULift.{v} M) :
    (F.ulift.connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm x.down :=
  F.pullbackDiffeomorph_curvatureTensorNorm _ t x

@[simp] theorem ulift_curvatureDerivativeNorm (F : RicciFlow n M J)
    (t : ℝ) (k : ℕ) (x : ULift.{v} M) :
    (F.ulift.connection t).curvatureDerivativeNorm k x =
      (F.connection t).curvatureDerivativeNorm k x.down :=
  F.pullbackDiffeomorph_curvatureDerivativeNorm _ t k x

@[simp] theorem ulift_nonnegativeCurvatureOperator_iff (F : RicciFlow n M J)
    (t : ℝ) (x : ULift.{v} M) :
    (F.ulift.connection t).NonnegativeCurvatureOperator x ↔
      (F.connection t).NonnegativeCurvatureOperator x.down :=
  F.pullbackDiffeomorph_nonnegativeCurvatureOperator_iff _ t x

@[simp] theorem ulift_edist (F : RicciFlow n M J)
    (t : ℝ) (x y : ULift.{v} M) :
    (F.ulift.metric t).edist x y = (F.metric t).edist x.down y.down :=
  F.pullbackDiffeomorph_edist _ t x y

theorem ulift_image_ball (F : RicciFlow n M J)
    (t : ℝ) (x : ULift.{v} M) (r : ℝ) :
    ULift.down '' (F.ulift.metric t).ball x r = (F.metric t).ball x.down r :=
  F.pullbackDiffeomorph_image_ball _ t x r

@[simp] theorem ulift_metricComplete_iff [T3Space M]
    (F : RicciFlow n M J) (t : ℝ) :
    MetricComplete ((F.ulift : RicciFlow n (ULift.{v} M) J).metric t) ↔
      MetricComplete (F.metric t) :=
  F.pullbackDiffeomorph_metricComplete_iff _ t

@[simp] theorem ulift_volumeMeasure_ball [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (F : RicciFlow n M J) (t : ℝ) (x : ULift.{v} M) (r : ℝ) :
    (F.ulift.metric t).volumeMeasure ((F.ulift.metric t).ball x r) =
      (F.metric t).volumeMeasure ((F.metric t).ball x.down r) :=
  F.pullbackDiffeomorph_volumeMeasure_ball _ t x r

end PoincareConjecture.RicciFlow
