import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.ParallelLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.TerminalFactor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open RiemannianMetric

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_lower_dimensional_ancient_flow_of_unbounded_scalar_ratio
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
    ∃ C : FlowCarrier.{u} m, NoncompactSpace C.carrier ∧
      ∃ H : RicciFlow m C.carrier (Iic 0), ∃ base : C.carrier, ∃ κ' : ℝ,
        0 < κ' ∧
        (∀ t ≤ 0, C.metricComplete (H.metric t)) ∧
        (∀ t ≤ 0, ∀ x, (H.connection t).NonnegativeCurvatureOperator x) ∧
        (∀ t ≤ 0, ∀ x,
          (H.connection t).curvatureTensorNorm x ≤ 4 * (((m + 1 : ℕ) : ℝ)) ^ 2) ∧
        0 < (H.connection 0).scalarCurvature base ∧
        0 < (H.metric 0).asymptoticVolumeRatio base ∧
        (∀ t ≤ 0, ∀ x, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (κ' * r ^ m) ≤ (H.metric t).volumeMeasure ((H.metric t).ball x r)) ∧
        (∀ t ≤ 0, ∀ x, ∀ r : ℝ, 0 < r →
          (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (H.metric t).ball x r,
            (H.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
          ENNReal.ofReal (κ' * r ^ m) ≤ (H.metric t).volumeMeasure ((H.metric t).ball x r)) := by
  obtain ⟨C, δ, hδ, _, G, base, hc, hop, hb, hs, hv,
      _, f, _, _, _, hf, hu, hz, _⟩ :=
    exists_nonflat_ancient_limit_with_terminal_parallel_gradient hm hC F
      hcomplete hoperator hK hbound hκ hnoncollapse ht₀ ht₁ htimeOrder p hvolume hunbounded
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let Ganc : RicciFlow (m + 1) C.carrier (Iic 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow G
      (fun _ ht => ht.trans_lt hδ) ordConnected_Iic
      ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  have hcAnc : ∀ t ≤ 0, MetricComplete (Ganc.metric t) :=
    fun t ht => hc t (ht.trans_lt hδ)
  have hopAnc : ∀ t ≤ 0, ∀ x, (Ganc.connection t).NonnegativeCurvatureOperator x :=
    fun t ht => hop t (ht.trans_lt hδ)
  have hbAnc : ∀ t ≤ 0, ∀ x,
      (Ganc.connection t).curvatureTensorNorm x ≤ 4 * (((m + 1 : ℕ) : ℝ)) ^ 2 :=
    fun t ht => hb t (ht.trans_lt hδ)
  have hB : 0 ≤ 4 * (((m + 1 : ℕ) : ℝ)) ^ 2 := by positivity
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens C.carrier)
    (fun x _ => regular_of_hasUnitGradient hu x) m 0
  let := isManifold_openLevelSet hf (⊤ : Opens C.carrier)
    (fun x _ => regular_of_hasUnitGradient hu x) m 0
  let H := Ganc.terminalParallelGradientFactor hC hcAnc hopAnc hB hbAnc hf hu hz
  obtain ⟨hk, _, hconn, hnc, hcomp, hcurv, hnorm,
      ⟨y, hscalar, hvolume⟩, hballs, hparabolic⟩ :=
    Ganc.terminalParallelGradientFactor_ancient_geometry hC hcAnc hopAnc hB hbAnc
      hf hu hz hm base hs hv
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let D : FlowCarrier.{u} m := FlowCarrier.ofConnectedManifold m (zeroLevelSet f)
  exact ⟨D, hnc, H, y, (Ganc.metric 0).asymptoticVolumeRatio base / 2 ^ (m + 2),
    hk, hcomp, hcurv, hnorm, hscalar, hvolume, hballs, hparabolic⟩

end PoincareConjecture.RicciFlow
