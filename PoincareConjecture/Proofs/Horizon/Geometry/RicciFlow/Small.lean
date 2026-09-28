import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Small
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Diffeomorph









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}

local instance smallCarrier : Small.{0} M :=
  Poincare.Topology.SecondCountable.small M

noncomputable local instance smallChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} M) :=
  Poincare.Manifold.shrinkChartedSpace _ M

local instance smallIsManifold : IsManifold (𝓡 n) ∞ (Shrink.{0} M) :=
  Poincare.Manifold.shrinkIsManifold (𝓡 n) M

local instance smallT3Space : T3Space (Shrink.{0} M) :=
  (Poincare.Topology.SecondCountable.homeomorphShrink M).t3Space


noncomputable def shrink (F : RicciFlow n M J) : RicciFlow n (Shrink.{0} M) J :=
  F.pullbackDiffeomorph (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm

@[simp] theorem shrink_scalarCurvature (F : RicciFlow n M J)
    (t : ℝ) (x : Shrink.{0} M) :
    (F.shrink.connection t).scalarCurvature x =
      (F.connection t).scalarCurvature ((equivShrink M).symm x) :=
  F.pullbackDiffeomorph_scalarCurvature _ t x

@[simp] theorem shrink_curvatureTensorNorm (F : RicciFlow n M J)
    (t : ℝ) (x : Shrink.{0} M) :
    (F.shrink.connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm ((equivShrink M).symm x) :=
  F.pullbackDiffeomorph_curvatureTensorNorm _ t x

@[simp] theorem shrink_nonnegativeCurvatureOperator_iff (F : RicciFlow n M J)
    (t : ℝ) (x : Shrink.{0} M) :
    (F.shrink.connection t).NonnegativeCurvatureOperator x ↔
      (F.connection t).NonnegativeCurvatureOperator ((equivShrink M).symm x) :=
  F.pullbackDiffeomorph_nonnegativeCurvatureOperator_iff _ t x

@[simp] theorem shrink_edist (F : RicciFlow n M J)
    (t : ℝ) (x y : Shrink.{0} M) :
    (F.shrink.metric t).edist x y =
      (F.metric t).edist ((equivShrink M).symm x) ((equivShrink M).symm y) :=
  F.pullbackDiffeomorph_edist _ t x y

theorem shrink_image_ball (F : RicciFlow n M J)
    (t : ℝ) (x : Shrink.{0} M) (r : ℝ) :
    (equivShrink M).symm '' (F.shrink.metric t).ball x r =
      (F.metric t).ball ((equivShrink M).symm x) r :=
  F.pullbackDiffeomorph_image_ball _ t x r

@[simp] theorem shrink_metricComplete_iff (F : RicciFlow n M J) (t : ℝ) :
    MetricComplete (F.shrink.metric t) ↔ MetricComplete (F.metric t) :=
  F.pullbackDiffeomorph_metricComplete_iff _ t

section Volume

variable [MeasurableSpace M] [BorelSpace M]

noncomputable local instance smallMeasurableSpace : MeasurableSpace (Shrink.{0} M) :=
  borel (Shrink.{0} M)

local instance smallBorelSpace : BorelSpace (Shrink.{0} M) := ⟨rfl⟩

@[simp] theorem shrink_volumeMeasure_ball (F : RicciFlow n M J)
    (t : ℝ) (x : Shrink.{0} M) (r : ℝ) :
    (F.shrink.metric t).volumeMeasure ((F.shrink.metric t).ball x r) =
      (F.metric t).volumeMeasure ((F.metric t).ball ((equivShrink M).symm x) r) :=
  F.pullbackDiffeomorph_volumeMeasure_ball _ t x r

end Volume

theorem shrink_scalarCurvature_mvfderiv (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M J) (t : ℝ) (x : Shrink.{0} M)
    (w : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => (F.shrink.connection t).scalarCurvature y) x w =
      mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y)
        ((equivShrink M).symm x)
        (mfderiv (𝓡 n) (𝓡 n)
          (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x w) :=
  F.pullbackDiffeomorph_scalarCurvature_mvfderiv hC _ t x w



theorem finite_harnack_shrink (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M J) (t T₀ dR : ℝ) (x : Shrink.{0} M)
    (w : TangentSpace (𝓡 n) x) :
    (HasDerivWithinAt (fun s => (F.shrink.connection s).scalarCurvature x) dR J t ∧
      0 ≤ dR + (F.shrink.connection t).scalarCurvature x / (t - T₀) +
        2 * mvfderiv (𝓡 n) (fun y => (F.shrink.connection t).scalarCurvature y) x w +
        2 * (F.shrink.connection t).ricci x w w) ↔
    (HasDerivWithinAt
        (fun s => (F.connection s).scalarCurvature ((equivShrink M).symm x)) dR J t ∧
      0 ≤ dR + (F.connection t).scalarCurvature ((equivShrink M).symm x) / (t - T₀) +
        2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y)
          ((equivShrink M).symm x)
          (mfderiv (𝓡 n) (𝓡 n)
            (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x w) +
        2 * (F.connection t).ricci ((equivShrink M).symm x)
          (mfderiv (𝓡 n) (𝓡 n)
            (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x w)
          (mfderiv (𝓡 n) (𝓡 n)
            (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x w)) :=
  F.finite_harnack_pullbackDiffeomorph hC _ t T₀ dR x w

end PoincareConjecture.RicciFlow
