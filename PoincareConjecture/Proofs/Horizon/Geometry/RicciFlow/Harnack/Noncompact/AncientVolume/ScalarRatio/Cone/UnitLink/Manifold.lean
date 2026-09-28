import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.RegularCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.OpenConeModel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8

open Set Filter TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace Poincare.AncientVolume.ScalarRatio

abbrev UnitSliceAmbient (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))



structure UnitSliceRadialChartData {X : Type*} [MetricSpace X] {p : X}
    (hcomparison : RayComparison p) (n : ℕ) where
  metric : RiemannianMetric (n + 1) (UnitSliceAmbient n)
  connection : LeviCivitaData metric
  potential : UnitSliceAmbient n → ℝ
  smooth : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ potential
  ambientChart : OpenPartialHomeomorph (UnitSliceAmbient n) (AsymptoticCone p hcomparison)
  positive : ∀ x ∈ ambientChart.source, 0 < potential x
  hessian : ∀ x ∈ ambientChart.source, ∀ v w,
    connection.hessian potential x v w = metric.inner x v w
  eikonal : ∀ x ∈ ambientChart.source, connection.levelQ potential x = 2 * potential x
  flat : ∀ x ∈ ambientChart.source, connection.curvatureTensorNorm x = 0
  radial : ∀ x ∈ ambientChart.source,
    (asymptoticConeRadius hcomparison (ambientChart x) : ℝ) ^ 2 / 2 = potential x
  distance : ∀ x ∈ ambientChart.source, ∀ y ∈ ambientChart.source,
    dist (ambientChart x) (ambientChart y) = (metric.edist x y).toReal

namespace UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}
  (d : UnitSliceRadialChartData hcomparison n)

def source : Opens (UnitSliceAmbient n) := ⟨d.ambientChart.source, d.ambientChart.open_source⟩

theorem regular : ∀ x ∈ d.source,
    mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) d.potential x ≠ 0 := by
  intro x hx hd
  have hg : d.connection.gradient d.potential x = 0 :=
    (d.metric.gradient_eq_zero_iff_mfderiv_eq_zero d.potential x).mpr hd
  have hz : d.connection.levelQ d.potential x = 0 := by
    simp only [LeviCivitaData.levelQ, hg, map_zero]
  rw [d.eikonal x hx] at hz
  linarith [d.positive x hx]

abbrev Level := openLevelSet d.potential d.source (1 / 2)

local instance ambient_finrank :
    Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩

instance levelChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) d.Level :=
  openLevelSetChartedSpace d.smooth d.source d.regular n (1 / 2)

instance levelIsManifold : IsManifold (𝓡 n) ∞ d.Level :=
  isManifold_openLevelSet d.smooth d.source d.regular n (1 / 2)

def target : Opens (AsymptoticConeUnitSlice p hcomparison) :=
  ⟨{z | z.1 ∈ d.ambientChart.target}, isOpen_unitLink_chart_target hcomparison d.ambientChart⟩

def levelHomeomorph : d.Level ≃ₜ d.target :=
  (openLevelSetHomeomorphLocalLevel d.potential d.source (1 / 2)).trans
    (unitLinkLocalLevelHomeomorph hcomparison d.ambientChart d.potential d.radial)

theorem levelHomeomorph_val (z : d.Level) :
    (d.levelHomeomorph z).1.1 = d.ambientChart (openLevelIncl d.potential d.source (1 / 2) z) := rfl



def levelEmbedding (z₀ : d.Level) :
    OpenPartialHomeomorph d.Level (AsymptoticConeUnitSlice p hcomparison) :=
  d.levelHomeomorph.toOpenPartialHomeomorph.trans
    (d.target.openPartialHomeomorphSubtypeCoe ⟨d.levelHomeomorph z₀⟩)

@[simp] theorem levelEmbedding_source (z₀ : d.Level) : (d.levelEmbedding z₀).source = univ := by
  simp [levelEmbedding]

@[simp] theorem levelEmbedding_target (z₀ : d.Level) : (d.levelEmbedding z₀).target = d.target := by
  simp [levelEmbedding]

theorem levelEmbedding_apply (z₀ z : d.Level) :
    d.levelEmbedding z₀ z = (d.levelHomeomorph z).1 := rfl



def chart (z : d.Level) :
    OpenPartialHomeomorph (AsymptoticConeUnitSlice p hcomparison) (EuclideanSpace ℝ (Fin n)) :=
  ((chartAt (EuclideanSpace ℝ (Fin n)) z).symm.trans (d.levelEmbedding z)).symm

theorem mem_chart_source (z : d.Level) : (d.levelHomeomorph z).1 ∈ (d.chart z).source := by
  let J := d.target.openPartialHomeomorphSubtypeCoe ⟨d.levelHomeomorph z⟩
  have hsource : chartAt (EuclideanSpace ℝ (Fin n)) z z ∈ (d.chart z).symm.source := by
    refine ⟨mem_chart_target (EuclideanSpace ℝ (Fin n)) z, ?_⟩
    change (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
      (chartAt (EuclideanSpace ℝ (Fin n)) z z) ∈
        (d.levelHomeomorph.toOpenPartialHomeomorph.trans J).source
    rw [(chartAt (EuclideanSpace ℝ (Fin n)) z).left_inv (_root_.mem_chart_source _ z)]
    change z ∈ Set.univ ∩ d.levelHomeomorph ⁻¹' J.source
    simp [J]
  have hvalue : (d.chart z).symm (chartAt (EuclideanSpace ℝ (Fin n)) z z) =
      (d.levelHomeomorph z).1 := by
    change (d.levelHomeomorph ((chartAt (EuclideanSpace ℝ (Fin n)) z).symm
      (chartAt (EuclideanSpace ℝ (Fin n)) z z))).1 = _
    rw [(chartAt (EuclideanSpace ℝ (Fin n)) z).left_inv (_root_.mem_chart_source _ z)]
  exact hvalue ▸ (d.chart z).symm.map_source hsource

theorem chart_source_subset_target (z : d.Level) : (d.chart z).source ⊆ d.target := by
  intro w hw
  simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hw.1.1

end UnitSliceRadialChartData


def unitSliceRadialAtlas {X : Type*} [MetricSpace X] {p : X}
    (hcomparison : RayComparison p) (n : ℕ) :
    Set (OpenPartialHomeomorph (AsymptoticConeUnitSlice p hcomparison) (EuclideanSpace ℝ (Fin n))) :=
  {C | ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level), C = d.chart z}



theorem exists_unitSliceRadialChartData_of_local_model
    {X : Type*} [MetricSpace X] {p : X} (hcomparison : RayComparison p)
    {n : ℕ} (g : RiemannianMetric (n + 1) (UnitSliceAmbient n)) (D : LeviCivitaData g)
    (f : UnitSliceAmbient n → ℝ)
    (H : OpenPartialHomeomorph (UnitSliceAmbient n) (AsymptoticCone p hcomparison))
    (hmodel : ∀ x ∈ H.source,
      0 < f x ∧ ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f x ∧
        D.curvatureTensorNorm x = 0 ∧
        (∀ v w, D.hessian f x v w = g.inner x v w) ∧ D.levelQ f x = 2 * f x)
    (hradial : ∀ x ∈ H.source, (asymptoticConeRadius hcomparison (H x) : ℝ) ^ 2 / 2 = f x)
    (hdistance : ∀ x ∈ H.source, ∀ y ∈ H.source, dist (H x) (H y) = (g.edist x y).toReal)
    {x : UnitSliceAmbient n} (hx : x ∈ H.source) :
    ∃ d : UnitSliceRadialChartData hcomparison n,
      x ∈ d.source ∧ d.potential x = f x ∧ d.ambientChart x = H x := by
  obtain ⟨ψ, hψ, heqnear⟩ := Poincare.Manifold.exists_contMDiff_eq_near H.open_source
    (fun y hy => (hmodel y hy).2.1.contMDiffWithinAt) hx
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ H.source := H.open_source.mem_nhds hx
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (heqnear.and hnear)
  have hVH : V ⊆ H.source := fun y hy => (hVsub hy).2
  have heq (y : UnitSliceAmbient n) (hy : y ∈ V) : ψ =ᶠ[𝓝 y] f := by
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact (hVsub hz).1
  let H' := H.restr V
  have hH'source : H'.source = V := by
    rw [OpenPartialHomeomorph.restr_source, hVo.interior_eq, inter_eq_right.mpr hVH]
  have hgrad (y : UnitSliceAmbient n) (hy : y ∈ V) : D.gradient ψ y = D.gradient f y := by
    simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq (heq y hy)]
  let d : UnitSliceRadialChartData hcomparison n := {
    metric := g
    connection := D
    potential := ψ
    smooth := hψ
    ambientChart := H'
    positive := fun y hy => by
      have hyV : y ∈ V := hH'source ▸ hy
      rw [(hVsub hyV).1]
      exact (hmodel y (hVH hyV)).1
    hessian := fun y hy v w => by
      have hyV : y ∈ V := hH'source ▸ hy
      rw [D.hessian_eq_of_eventuallyEq (heq y hyV)]
      exact (hmodel y (hVH hyV)).2.2.2.1 v w
    eikonal := fun y hy => by
      have hyV : y ∈ V := hH'source ▸ hy
      change g.inner y (D.gradient ψ y) (D.gradient ψ y) = 2 * ψ y
      rw [hgrad y hyV, (hVsub hyV).1]
      exact (hmodel y (hVH hyV)).2.2.2.2
    flat := fun y hy => (hmodel y (hVH (hH'source ▸ hy))).2.2.1
    radial := fun y hy =>
      (hradial y (hVH (hH'source ▸ hy))).trans (hVsub (hH'source ▸ hy)).1.symm
    distance := fun y hy z hz => hdistance y (hVH (hH'source ▸ hy)) z (hVH (hH'source ▸ hz)) }
  exact ⟨d, by change x ∈ H'.source; rwa [hH'source], heqnear.self_of_nhds, rfl⟩



@[instance_reducible] def unitSliceChartedSpace {X : Type*} [MetricSpace X] {p : X}
    (hcomparison : RayComparison p) (n : ℕ)
    (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (AsymptoticConeUnitSlice p hcomparison) where
  atlas := unitSliceRadialAtlas hcomparison n
  chartAt x := (hcover x).choose.chart (hcover x).choose_spec.choose
  mem_chart_source x := by
    have h := (hcover x).choose.mem_chart_source (hcover x).choose_spec.choose
    rwa [(hcover x).choose_spec.choose_spec] at h
  chart_mem_atlas x := ⟨(hcover x).choose, (hcover x).choose_spec.choose, rfl⟩

theorem unitSliceChartedSpace_atlas {X : Type*} [MetricSpace X] {p : X}
    (hcomparison : RayComparison p) (n : ℕ)
    (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    (unitSliceChartedSpace hcomparison n hcover).atlas = unitSliceRadialAtlas hcomparison n := rfl

end Poincare.AncientVolume.ScalarRatio

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
  (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
  (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
  {K : ℝ} (hK : 0 ≤ K)
  (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
  {κ : ℝ} (hκ : 0 < κ)
  (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
    (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
      (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
    ENNReal.ofReal (κ * r ^ (n + 1)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
  (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
  (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
    L ≤ ((F.metric t₀).edist p x).toReal →
    (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)

include hC hK hbound hκ hnoncollapse hzero



theorem unitSliceRadialAtlas_covers_of_zero_ratio :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    ∀ x : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
        (d.levelHomeomorph z).1 = x := by
  let := (F.metric t₀).toMetricSpace
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  dsimp only
  intro x
  obtain ⟨l, hl⟩ := surjective_asymptoticConeUnitProjection hcomparison x
  obtain ⟨η, hη⟩ := surjective_asymptoticLinkProjection hcomparison l
  have hxcone : asymptoticConeRayProjection hcomparison (1, η) = x.1 := by
    have hv := congrArg Subtype.val hl
    rw [← hη] at hv
    exact hv
  obtain ⟨g, D, f, r, δ, hr, _, _, _, _, hf0, hmodel,
    H, _, _, hH0, hzeroH, hHsmall, hradial, hdistance, _⟩ :=
    F.exists_open_flat_radial_cone_model_along_ray_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse (Nat.le_add_left 1 n) t₀ ht₀ p hzero η
  have hmodelH : ∀ y ∈ H.source,
      0 < f y ∧ ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f y ∧
        D.curvatureTensorNorm y = 0 ∧
        (∀ v w, D.hessian f y v w = g.inner y v w) ∧ D.levelQ f y = 2 * f y := by
    intro y hy
    exact hmodel y (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r) (hHsmall hy))
  obtain ⟨d, hdzero, hdf0, hdH0⟩ := exists_unitSliceRadialChartData_of_local_model
    hcomparison g D f H hmodelH (fun y hy => (hradial y hy).symm) hdistance hzeroH
  let z : d.Level := ⟨⟨0, hdzero⟩, hdf0.trans hf0⟩
  refine ⟨d, z, Subtype.ext ?_⟩
  rw [d.levelHomeomorph_val]
  exact hdH0.trans (hH0.trans hxcone)



@[instance_reducible] def unitSliceChartedSpace_of_zero_ratio :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (AsymptoticConeUnitSlice p hcomparison) := by
  letI := (F.metric t₀).toMetricSpace
  exact unitSliceChartedSpace _ n
    (F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero)



theorem unitSlice_topology_of_zero_ratio :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) (AsymptoticConeUnitSlice p hcomparison)) ∧
      Nonempty (AsymptoticConeUnitSlice p hcomparison) ∧
      CompactSpace (AsymptoticConeUnitSlice p hcomparison) ∧
      SecondCountableTopology (AsymptoticConeUnitSlice p hcomparison) := by
  let := (F.metric t₀).toMetricSpace
  let := (F.metric t₀).properSpace_toMetricSpace (hcomplete t₀ ht₀)
  dsimp only
  refine ⟨⟨F.unitSliceChartedSpace_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero⟩, ?_, inferInstance, inferInstance⟩
  exact nonempty_asymptoticConeUnitSlice _
    ((F.metric t₀).nonempty_basedMinimizingRays (hcomplete t₀ ht₀) p)

end PoincareConjecture.RicciFlow
