import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SmallRescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]


structure SpatialLineLimit (F : RicciFlow 3 M (Iic 0)) (t₀ : ℝ) (p : M) where
  centers : ℕ → M
  scalar_pos : ∀ i, 0 < (F.connection t₀).scalarCurvature (centers i)
  centers_escape : Tendsto (fun i => ((F.metric t₀).edist p (centers i)).toReal)
    atTop atTop
  scales_bounded : BddAbove (range (fun i => (F.connection t₀).scalarCurvature (centers i)))
  buffer : ℝ
  buffer_pos : 0 < buffer
  buffer_lt_one : buffer < 1
  convergence : AncientPointedGeometricConvergence
    (fun _ => (FlowCarrier.ofConnectedManifold 3 M).shrink)
    (fun i t => (F.interiorAncientRescaleAt
      ((F.connection t₀).scalarCurvature (centers i)) (scalar_pos i) t₀).shrink.metric
        (t - buffer))
    (fun i => equivShrink M (centers i)) buffer
  complete : ∀ t ∈ Iio buffer,
    convergence.limitCarrier.metricComplete (convergence.limitFlow.metric t)
  nonnegative_curvature : ∀ t ∈ Iio buffer, ∀ x,
    (convergence.limitFlow.connection t).NonnegativeCurvatureOperator x
  curvature_bound : ∀ t ∈ Iio buffer, ∀ x,
    (convergence.limitFlow.connection t).curvatureTensorNorm x ≤ 36
  nonflat : 0 < (convergence.limitFlow.connection 0).curvatureTensorNorm convergence.base
  line : letI := convergence.limitCarrier.metricSpaceOf (convergence.limitFlow.metric 0)
    ∃ γ : ℝ → convergence.limitCarrier.carrier, Isometry γ ∧ γ 0 = convergence.base


theorem SpatialLineLimit.scalarCurvature_pos
    {F : RicciFlow 3 M (Iic 0)} {t₀ : ℝ} {p : M}
    (L : SpatialLineLimit F t₀ p) (hC : RicciFlowCurvatureTheory.{u}) :
    0 < (L.convergence.limitFlow.connection 0).scalarCurvature L.convergence.base := by
  let C := L.convergence.limitCarrier
  let F₀ := L.convergence.limitFlow
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) C.carrier
  let H : RicciFlow 3 (ULift.{u} C.carrier) (Iio L.buffer) := F₀.ulift
  have hD := hC.tensor_calculus 3 (ULift.{u} C.carrier) (H.metric 0) (H.connection 0)
  have hop := (F₀.ulift_nonnegativeCurvatureOperator_iff 0
    (ULift.up.{u} L.convergence.base)).mpr
      (L.nonnegative_curvature 0 L.buffer_pos L.convergence.base)
  have hbound := (H.connection 0).curvatureTensorNorm_le_scalarCurvature hD
    (ULift.up.{u} L.convergence.base) hop
  simp only [H, F₀.ulift_curvatureTensorNorm, F₀.ulift_scalarCurvature] at hbound
  have hn := L.nonflat
  change 0 < (F₀.connection 0).curvatureTensorNorm L.convergence.base at hn
  change 0 < (F₀.connection 0).scalarCurvature L.convergence.base
  norm_num at hbound
  linarith

set_option maxHeartbeats 800000 in


theorem exists_spatialLineLimit_of_unbounded_scalar_ratio
    [NoncompactSpace M] (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow 3 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ < 0) (p : M)
    (hunbounded : ¬ BddAbove (range (fun x =>
      ((F.metric t₀).edist p x).toReal ^ 2 * (F.connection t₀).scalarCurvature x))) :
    Nonempty (SpatialLineLimit F t₀ p) := by
  obtain ⟨q, r, hQ, hcontrol, hd, _, hL, hdQ, hratio, hQbound, _, _, _, _, _, _,
      ν, _, _, δ, hδ, hδone, G, hGcomplete, hnonflat, hGnorm, hGoperator⟩ :=
    exists_nonflat_small_ancient_rescaled_limit_of_unbounded_scalar_ratio
      (m := 2) (by norm_num) hC F hcomplete hoperator hK hbound hκ hnoncollapse
      t₀ ht₀ p hunbounded
  let Q := fun i => (F.connection t₀).scalarCurvature (q i)
  have hline := exists_isometric_line_of_selected_small_rescalings hC (m := 2)
    (by norm_num) F hcomplete hoperator hK hbound t₀ ht₀ p q r Q
    (fun i => (hcontrol i).1) hQ (fun i => (hcontrol i).2.1)
    hd hdQ hL hratio hδ G (hGcomplete 0 hδ)
  refine ⟨{
    centers := q
    scalar_pos := hQ
    centers_escape := hd
    scales_bounded := hQbound
    buffer := δ
    buffer_pos := hδ
    buffer_lt_one := hδone
    convergence := G
    complete := hGcomplete
    nonnegative_curvature := hGoperator
    nonflat := hnonflat
    line := hline
    curvature_bound := ?_ }⟩
  norm_num at hGnorm
  exact hGnorm

end PoincareConjecture.RicciFlow
