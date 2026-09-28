import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gluing.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Geometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture Manifold IsManifold
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hc : RayComparison p} {n : ℕ}

def UnitSliceRadialChartData.sourceMetric (d : UnitSliceRadialChartData hc n) :
    RiemannianMetric (n + 1) d.source :=
  d.metric.pullbackOfLocalDiffeomorph Subtype.val
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) d.source)

@[simp] theorem UnitSliceRadialChartData.sourceMetric_inner
    (d : UnitSliceRadialChartData hc n) (x : d.source)
    (v w : TangentSpace (𝓡 (n + 1)) x) :
    d.sourceMetric.inner x v w = d.metric.inner x v w := by
  simp only [sourceMetric, RiemannianMetric.pullbackOfLocalDiffeomorph_inner,
    mfderiv_opens_subtypeVal_apply]

variable (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)

theorem exists_unique_positiveConeMetric :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∃! gP : RiemannianMetric (n + 1) (AsymptoticConePositive p hc),
      ∀ (d : UnitSliceRadialChartData hc n) (x : d.source)
        (v w : TangentSpace (𝓡 (n + 1)) x),
        d.metric.inner x v w = gP.inner (d.positiveMap x)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x v)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x w) := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  have hq (d : UnitSliceRadialChartData hc n) :
      IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ d.positiveMap :=
    d.isLocalDiffeomorph_positiveMap hne hcover
  have hcov (a : AsymptoticConePositive p hc) :
      ∃ (d : UnitSliceRadialChartData hc n) (x : d.source), d.positiveMap x = a := by
    obtain ⟨d, x, hx, hvalue, _⟩ := exists_dilated_radial_model_at_positive_point hc hcover a
    exact ⟨d.dilate (asymptoticConeRadius hc a.1) a.property, ⟨x, hx⟩, Subtype.ext hvalue⟩
  have hdescent := Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms
    (fun d : UnitSliceRadialChartData hc n => d.sourceMetric)
    (fun d => d.positiveMap) hq hcov
  simp only [UnitSliceRadialChartData.sourceMetric_inner] at hdescent
  apply hdescent
  intro d e x y hxy a b a' b' ha hb
  let T := d.ambientChart.trans e.ambientChart.symm
  have hyvalue : e.ambientChart.symm (d.ambientChart x) = y := by
    have h := congrArg Subtype.val hxy
    change d.ambientChart x = e.ambientChart y at h
    rw [h, e.ambientChart.left_inv y.property]
  have hxT : (x : UnitSliceAmbient n) ∈ T.source := by
    refine ⟨x.property, ?_⟩
    change d.ambientChart x ∈ e.ambientChart.target
    have h := congrArg Subtype.val hxy
    change d.ambientChart x = e.ambientChart y at h
    rw [h]
    exact e.ambientChart.map_source y.property
  have hT := d.metric.smooth_isometric_charts_of_edist_eq e.metric T
    (d.metric.edist_eq_on_isometric_chart_transition e.metric
      d.ambientChart e.ambientChart d.distance e.distance)
  let C := e.positiveChart hne
  have hmax : C ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨e, rfl⟩
  have hxC : d.positiveMap x ∈ C.source := by
    rw [hxy]
    change e.positiveMap y ∈ (e.positiveChart hne).source
    rw [e.positiveChart_source]
    exact e.ambientChart.map_source y.property
  have hCd : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) C (d.positiveMap x) :=
    ((contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (C.open_source.mem_nhds hxC)).mdifferentiableAt
      (by simp)
  have hCe : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) C (e.positiveMap y) := by
    rwa [hxy] at hCd
  have hDT (v : TangentSpace (𝓡 (n + 1)) x) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) C (d.positiveMap x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x v) =
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x v := by
    have hh := mfderiv_comp x hCd ((hq d).mdifferentiable (by simp) x)
    have hrestrict := mfderiv_opens_restrict d.source T
      ((hT.1.contMDiffAt (T.open_source.mem_nhds hxT)).mdifferentiableAt (by simp))
    exact (congrArg (fun L => L v) hh).symm.trans (congrArg (fun L => L v) hrestrict)
  have hDI (v : TangentSpace (𝓡 (n + 1)) y) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) C (e.positiveMap y)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e.positiveMap y v) = v := by
    have hh := mfderiv_comp y hCe ((hq e).mdifferentiable (by simp) y)
    have hfun : C ∘ e.positiveMap = (Subtype.val : e.source → UnitSliceAmbient n) := by
      funext z
      exact e.ambientChart.left_inv z.property
    rw [hfun] at hh
    have hv := congrArg (fun L => L v) hh.symm
    simp only [mfderiv_opens_subtypeVal_apply] at hv
    convert! hv using 1
  have hda : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x a = a' := by
    rw [← hDT, ha, hxy]
    exact hDI a'
  have hdb : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x b = b' := by
    rw [← hDT, hb, hxy]
    exact hDI b'
  have hm := hT.2.2 x hxT a b
  change e.metric.inner (e.ambientChart.symm (d.ambientChart x)) _ _ = _ at hm
  rw [hyvalue, hda, hdb] at hm
  exact hm.symm

def positiveConeMetric :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    RiemannianMetric (n + 1) (AsymptoticConePositive p hc) :=
  (exists_unique_positiveConeMetric hne hcover).exists.choose

theorem positiveConeMetric_inner :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ (d : UnitSliceRadialChartData hc n) (x : d.source)
      (v w : TangentSpace (𝓡 (n + 1)) x),
      d.metric.inner x v w = (positiveConeMetric hne hcover).inner (d.positiveMap x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x v)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x w) :=
  (exists_unique_positiveConeMetric hne hcover).exists.choose_spec

theorem positiveConeMetric_curvatureTensorNorm_eq_zero :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ a : AsymptoticConePositive p hc,
      (positiveConeMetric hne hcover).leviCivitaData.curvatureTensorNorm a = 0 := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  obtain ⟨d, x, hx, hvalue, _⟩ := exists_dilated_radial_model_at_positive_point hc hcover a
  let e := d.dilate (asymptoticConeRadius hc a.1) a.property
  let y : e.source := ⟨x, hx⟩
  have hya : e.positiveMap y = a := Subtype.ext hvalue
  have hflat : e.sourceMetric.leviCivitaData.curvatureTensorNorm y = 0 := by
    have hR := e.sourceMetric.leviCivitaData.curvatureTensorNorm_eq_of_local_isometry
      e.connection isOpen_univ contMDiff_subtype_val.contMDiffOn
      (fun z _ v w => by simp only [UnitSliceRadialChartData.sourceMetric_inner,
        mfderiv_opens_subtypeVal_apply]) (Set.mem_univ y)
    exact hR.trans (e.flat y y.property)
  have hR := e.sourceMetric.leviCivitaData.curvatureTensorNorm_eq_of_local_isometry
    (positiveConeMetric hne hcover).leviCivitaData isOpen_univ
    (e.isLocalDiffeomorph_positiveMap hne hcover).contMDiff.contMDiffOn
    (fun z _ v w => by
      rw [e.sourceMetric_inner]
      exact positiveConeMetric_inner hne hcover e z v w) (Set.mem_univ y)
  rw [hya] at hR
  exact hR.symm.trans hflat

end Poincare.AncientVolume.ScalarRatio

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio

theorem positiveCone_geometry_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
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
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
    let hne := nonempty_asymptoticConePositive_of_unitSlice hc
      (nonempty_asymptoticConeUnitSlice hc
        ((F.metric t₀).nonempty_basedMinimizingRays (hcomplete t₀ ht₀) p))
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    let gP := positiveConeMetric hne hcover
    IsManifold (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) ∧
      (∀ a : AsymptoticConePositive p hc, gP.leviCivitaData.curvatureTensorNorm a = 0) ∧
      (∀ (d : UnitSliceRadialChartData hc n) (x : d.source)
        (v w : TangentSpace (𝓡 (n + 1)) x),
        d.metric.inner x v w = gP.inner (d.positiveMap x)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x v)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x w)) ∧
      (∀ (d : UnitSliceRadialChartData hc n) (x y : d.source),
        dist (d.positiveMap x) (d.positiveMap y) = (d.metric.edist x y).toReal) := by
  let := (F.metric t₀).toMetricSpace
  dsimp only
  exact ⟨positiveCone_isManifold _ _ _ _, positiveConeMetric_curvatureTensorNorm_eq_zero _ _,
    positiveConeMetric_inner _ _, fun d x y => d.positiveMap_distance x y⟩

end PoincareConjecture.RicciFlow
