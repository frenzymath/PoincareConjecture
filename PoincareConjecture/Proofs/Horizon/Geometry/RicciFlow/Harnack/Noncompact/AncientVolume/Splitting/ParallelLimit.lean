import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.NonflatLineLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Main
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
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

set_option maxHeartbeats 800000 in

theorem exists_nonflat_ancient_limit_with_terminal_parallel_gradient
    {m : ℕ} (hm : 0 < m) {M : Type u}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (m + 1)) ≤
        (F.metric t).volumeMeasure ((F.metric t).ball x r))
    {t₀ t₁ : ℝ} (ht₀ : t₀ < 0) (ht₁ : t₁ ≤ 0) (htimeOrder : t₀ ≤ t₁)
    (p : M) (hvolume : 0 < (F.metric t₁).asymptoticVolumeRatio p)
    (hunbounded : ¬ BddAbove (range (fun x =>
      ((F.metric t₀).edist p x).toReal ^ 2 * (F.connection t₀).scalarCurvature x))) :
    ∃ C : FlowCarrier.{u} (m + 1), ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ Flim : RicciFlow (m + 1) C.carrier (Iio δ), ∃ base : C.carrier,
        (∀ t ∈ Iio δ, C.metricComplete (Flim.metric t)) ∧
        (∀ t ∈ Iio δ, ∀ x, (Flim.connection t).NonnegativeCurvatureOperator x) ∧
        (∀ t ∈ Iio δ, ∀ x,
          (Flim.connection t).curvatureTensorNorm x ≤ 4 * (((m + 1 : ℕ) : ℝ)) ^ 2) ∧
        0 < (Flim.connection 0).scalarCurvature base ∧
        0 < (Flim.metric 0).asymptoticVolumeRatio base ∧
        ∃ (γ : ℝ → C.carrier) (f : C.carrier → ℝ),
          γ 0 = base ∧
          (∀ s t : ℝ, (Flim.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
          f = (Flim.metric 0).busemann γ ∧
          ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ f ∧
          RiemannianMetric.HasUnitGradient (Flim.connection 0) f ∧
          RiemannianMetric.HasZeroHessian (Flim.connection 0) f ∧ f base = 0 := by
  obtain ⟨C, δ, hδ, hδone, H, base, hc, hop, hnorm, hscalar, hAVR, hline⟩ :=
    exists_nonflat_small_ancient_limit_with_line_of_unbounded_scalar_ratio hm hC F
      hcomplete hoperator hK hbound hκ hnoncollapse ht₀ ht₁ htimeOrder p hvolume hunbounded
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let : ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  let : IsManifold (𝓡 (m + 1)) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 (m + 1)) C.carrier
  let : ConnectedSpace (ULift.{u} C.carrier) :=
    (Homeomorph.ulift.connectedSpace_iff).mpr inferInstance
  let : SecondCountableTopology (ULift.{u} C.carrier) :=
    Homeomorph.ulift.secondCountableTopology
  let L : FlowCarrier.{u} (m + 1) :=
    FlowCarrier.ofConnectedManifold (m + 1) (ULift.{u} C.carrier)
  let Hlift : RicciFlow (m + 1) (ULift.{u} C.carrier) (Iio δ) := H.ulift
  let := C.metricSpaceOf (H.metric 0)
  obtain ⟨γ, hγ, hγ0⟩ := hline
  let γlift : ℝ → ULift.{u} C.carrier := fun s => ULift.up.{u} (γ s)
  have hγlift0 : γlift 0 = ULift.up.{u} base := congrArg ULift.up hγ0
  have hγlift : ∀ s t : ℝ, (Hlift.metric 0).edist (γlift s) (γlift t) =
      ENNReal.ofReal |s - t| := by
    intro s t
    rw [show (Hlift.metric 0).edist (γlift s) (γlift t) =
      (H.metric 0).edist (γ s) (γ t) by exact H.ulift_edist 0 _ _]
    change edist (γ s) (γ t) = ENNReal.ofReal |s - t|
    rw [hγ.edist_eq, edist_dist, Real.dist_eq]
  have hcLift (t : ℝ) (ht : t ∈ Iio δ) : MetricComplete (Hlift.metric t) :=
    (H.ulift_metricComplete_iff t).mpr (hc t ht)
  have hopLift (t : ℝ) (ht : t ∈ Iio δ) (x : ULift.{u} C.carrier) :
      (Hlift.connection t).NonnegativeCurvatureOperator x :=
    (H.ulift_nonnegativeCurvatureOperator_iff t x).mpr (hop t ht x.down)
  have hRic : (Hlift.connection 0).NonnegativeRicciCurvature := by
    intro x v
    exact ((Hlift.connection 0).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) (ULift.{u} C.carrier)
        (Hlift.metric 0) (Hlift.connection 0)) x (hopLift 0 hδ x) v).1
  obtain ⟨hf, hu, _, hz, hf0⟩ := (Hlift.metric 0).busemann_parallel_unit_gradient
    (Hlift.connection 0) (hcLift 0 hδ) hRic hγlift
  have hAVRLift : (Hlift.metric 0).asymptoticVolumeRatio (ULift.up.{u} base) =
      (H.metric 0).asymptoticVolumeRatio base := by
    simp only [RiemannianMetric.asymptoticVolumeRatio, Hlift, H.ulift_volumeMeasure_ball]
  refine ⟨L, δ, hδ, hδone, Hlift, ULift.up.{u} base, hcLift, hopLift, ?_, ?_,
    hAVRLift.symm ▸ hAVR, γlift, (Hlift.metric 0).busemann γlift,
    hγlift0, hγlift, rfl, hf, hu, hz, ?_⟩
  · intro t ht x
    simpa only [Hlift, H.ulift_curvatureTensorNorm] using hnorm t ht x.down
  · simpa only [Hlift, H.ulift_scalarCurvature] using hscalar
  · simpa only [hγlift0] using hf0

end PoincareConjecture.RicciFlow
