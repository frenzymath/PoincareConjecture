import PoincareConjecture.Proofs.M10.SmoothMetric
import PoincareConjecture.Proofs.M10.ProductDerivatives
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.Deriv.Mul









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem coordinateBackwardMetric_at_center (q : M) (τ : ℝ)
    (v w : TangentSpace (𝓡 n) q) :
    coordinateBackwardMetric F T q (extChartAt (𝓡 n) q q, τ) v w =
      (F.metric (T - τ)).inner q v w := by
  have hc := backwardMetricCoordinates_apply (F := F) (T := T) q (q, τ)
    (FiberBundle.mem_baseSet_trivializationAt' q) v w
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ _),
    mfderiv_extChartAt_self] at hc
  simpa only [coordinateBackwardMetric, extChartAt_to_inv,
    ContinuousLinearMap.id_apply] using! hc


theorem backward_metric_inner_hasDerivAt
    (hwindow : Icc (T - τmax) T ⊆ J) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (q : M) (v w : TangentSpace (𝓡 n) q) :
    HasDerivAt (fun s ↦ (F.metric (T - s)).inner q v w)
      (2 * (F.connection (T - τ)).ricci q v w) τ := by
  have hi : T - τ ∈ Ioo (T - τmax) T := by constructor <;> linarith
  have hJ : J ∈ 𝓝 (T - τ) :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hi)
      (fun _ hs ↦ hwindow ⟨hs.1.le, hs.2.le⟩)
  have hd := (F.equation (T - τ) (hwindow ⟨hi.1.le, hi.2.le⟩) q v w).hasDerivAt hJ
  have ht := hd.comp τ ((hasDerivAt_id τ).const_sub T)
  simpa only [Function.comp_def, neg_mul, mul_neg, mul_one, neg_neg] using ht

set_option backward.isDefEq.respectTransparency false in

theorem coordinateBackwardMetric_time_derivative
    (hwindow : Icc (T - τmax) T ⊆ J) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (q : M) (v w : TangentSpace (𝓡 n) q) :
    fderiv ℝ (coordinateBackwardMetric F T q) (extChartAt (𝓡 n) q q, τ) (0, 1) v w =
      2 * (F.connection (T - τ)).ricci q v w := by
  let v' : EuclideanSpace ℝ (Fin n) := v
  let w' : EuclideanSpace ℝ (Fin n) := w
  have hB : DifferentiableAt ℝ (coordinateBackwardMetric F T q)
      (extChartAt (𝓡 n) q q, τ) :=
    (coordinateBackwardMetric_contDiffAt (F := F) hwindow q hτ hmax).differentiableAt (by simp)
  have ht := hasDerivAt_time_slice (X := EuclideanSpace ℝ (Fin n))
    (Y := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hB
  have hv := ht.clm_apply (hasDerivAt_const τ v')
  have hcoord := hv.clm_apply (hasDerivAt_const τ w')
  simp only [map_zero, add_zero] at hcoord
  have hmetric := (backward_metric_inner_hasDerivAt hwindow hτ hmax q v w).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s ↦
      coordinateBackwardMetric_at_center (F := F) (T := T) q s v w))
  exact hcoord.unique hmetric

end PoincareConjecture.M10
