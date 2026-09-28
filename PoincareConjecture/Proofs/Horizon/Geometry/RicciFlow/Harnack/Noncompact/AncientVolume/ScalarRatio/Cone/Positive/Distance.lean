import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactConfinement
import Mathlib.Topology.UnitInterval
















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory TopologicalSpace PoincareConjecture Manifold IsManifold
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hc : RayComparison p} {n : ℕ}

variable (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)



theorem exists_positiveCone_local_ambient_realization :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ a : AsymptoticConePositive p hc,
      ∃ (U : Set (AsymptoticConePositive p hc)), IsOpen U ∧ a ∈ U ∧
        ∃ (h : RiemannianMetric (n + 1) (UnitSliceAmbient n))
          (F : AsymptoticConePositive p hc → UnitSliceAmbient n),
          ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ F U ∧
          (∀ y ∈ U, ∀ v w,
            (positiveConeMetric hne hcover).inner y v w = h.inner (F y)
              (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) F y v)
              (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) F y w)) ∧
          ∀ y ∈ U, ∀ z ∈ U, edist y z = h.edist (F y) (F z) := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  obtain ⟨d₀, x, hx, ha, _⟩ := exists_dilated_radial_model_at_positive_point hc hcover a
  let d := d₀.dilate (asymptoticConeRadius hc a.1) a.property
  let x₀ : d.source := ⟨x, hx⟩
  have hx₀ : d.positiveMap x₀ = a := Subtype.ext ha
  let q := d.positiveMap
  have hq := d.isLocalDiffeomorph_positiveMap hne hcover
  let e := (hq x₀).localInverse
  let incl := (Subtype.val : d.source → UnitSliceAmbient n)
  have hi : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ incl := contMDiff_subtype_val
  have he := e.contMDiffOn
  have hright (y : AsymptoticConePositive p hc) (hy : y ∈ e.source) : q (e y) = y :=
    (hq x₀).localInverse_right_inv hy
  refine ⟨e.source, e.open_source, hx₀ ▸ (hq x₀).localInverse_mem_source,
    d.metric, incl ∘ e, hi.comp_contMDiffOn he, ?_, ?_⟩
  · intro y hy v w
    have hediff := e.mdifferentiableAt (by simp) hy
    have hcomp : (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) q (e y)).comp
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y) = ContinuousLinearMap.id ℝ _ := by
      rw [← mfderiv_comp y (hq.mdifferentiable (by simp) (e y)) hediff]
      have hgerm : q ∘ e =ᶠ[𝓝 y] id :=
        Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) hright
      rw [hgerm.mfderiv_eq, mfderiv_id]
    have hm := positiveConeMetric_inner hne hcover d (e y)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y v)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y w)
    have hv : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) q (e y)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y v) = v :=
      congrArg (fun A : UnitSliceAmbient n →L[ℝ] UnitSliceAmbient n => A v) hcomp
    have hw : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) q (e y)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y w) = w :=
      congrArg (fun A : UnitSliceAmbient n →L[ℝ] UnitSliceAmbient n => A w) hcomp
    change d.metric.inner (e y) _ _ = (positiveConeMetric hne hcover).inner (q (e y))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) q (e y)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y v))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) q (e y)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e y w)) at hm
    rw [hv, hw, hright y hy] at hm
    rw [← hm, mfderiv_comp y (hi.mdifferentiable (by simp) (e y)) hediff]
    rw [show mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) incl (e y) =
      ContinuousLinearMap.id ℝ (UnitSliceAmbient n) from mfderiv_opens_subtypeVal d.source (e y)]
    rfl
  · intro y hy z hz
    have heq : dist y z = (d.metric.edist (incl (e y)) (incl (e z))).toReal := by
      calc
        dist y z = dist (q (e y)) (q (e z)) := by rw [hright y hy, hright z hz]
        _ = _ := d.positiveMap_distance (e y) (e z)
    rw [edist_dist, heq, ENNReal.ofReal_toReal (d.metric.edist_ne_top _ _)]
    rfl

private theorem positive_pathELength_comp_eq_on
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {a b : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin a)) A] [ChartedSpace (EuclideanSpace ℝ (Fin b)) B]
    [IsManifold (𝓡 a) ∞ A] [IsManifold (𝓡 b) ∞ B]
    (g : RiemannianMetric a A) (h : RiemannianMetric b B)
    {U : Set A} (hU : IsOpen U) {F : A → B}
    (hF : ContMDiffOn (𝓡 a) (𝓡 b) ∞ F U)
    (hm : ∀ x ∈ U, ∀ v w, g.inner x v w = h.inner (F x)
      (mfderiv (𝓡 a) (𝓡 b) F x v) (mfderiv (𝓡 a) (𝓡 b) F x w))
    {γ : ℝ → A} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 a) 1 γ)
    {s t : ℝ} (hγU : MapsTo γ (Icc s t) U) :
    h.pathELength (F ∘ γ) s t = g.pathELength γ s t := by
  rw [h.pathELength_eq_lintegral_tangentNorm, g.pathELength_eq_lintegral_tangentNorm]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  have hFx := (hF.contMDiffAt (hU.mem_nhds (hγU hu))).mdifferentiableAt (by simp)
  rw [mfderiv_comp u hFx (hγ.mdifferentiable one_ne_zero u)]
  change ENNReal.ofReal (Real.sqrt (h.inner (F (γ u)) _ _)) =
    ENNReal.ofReal (Real.sqrt (g.inner (γ u) _ _))
  rw [hm _ (hγU hu)]
  rfl


theorem positiveCone_edist_le_pathELength :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ γ : ℝ → AsymptoticConePositive p hc,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 γ →
      edist (γ 0) (γ 1) ≤ (positiveConeMetric hne hcover).pathELength γ 0 1 := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro γ hγ
  let g := positiveConeMetric hne hcover
  choose U hU hx h F hF hm hd using exists_positiveCone_local_ambient_realization hne hcover
  let c := fun x => (fun t : unitInterval => γ t) ⁻¹' U x
  have hcopen : ∀ x, IsOpen (c x) := fun x =>
    (hU x).preimage (hγ.continuous.comp continuous_subtype_val)
  have hccover : univ ⊆ ⋃ x, c x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, hx (γ t)⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover
  have hstep (k : ℕ) : edist (γ (t k)) (γ (t (k + 1))) ≤
      g.pathELength γ (t k) (t (k + 1)) := by
    obtain ⟨x, htx⟩ := hsub k
    have htime : (t k : ℝ) ≤ t (k + 1) := htmono (Nat.le_succ k)
    have hγU : MapsTo γ (Icc (t k : ℝ) (t (k + 1))) (U x) := by
      intro s hs
      have hsunit : s ∈ unitInterval :=
        ⟨(t k).property.1.trans hs.1, hs.2.trans (t (k + 1)).property.2⟩
      exact htx (show (⟨s, hsunit⟩ : unitInterval) ∈ Icc (t k) (t (k + 1)) from hs)
    rw [hd x _ (hγU ⟨le_rfl, htime⟩) _ (hγU ⟨htime, le_rfl⟩)]
    have hmap : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1
        (F x ∘ γ) (Icc (t k : ℝ) (t (k + 1))) :=
      ((hF x).of_le (by simp)).comp hγ.contMDiffOn hγU
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 (n + 1)) : UnitSliceAmbient n → Type _) :=
      ⟨(h x).toRiemannianMetric⟩
    exact (Manifold.riemannianEDist_le_pathELength (I := 𝓡 (n + 1))
      (γ := F x ∘ γ) hmap rfl rfl htime).trans_eq
      (positive_pathELength_comp_eq_on g (h x) (hU x) (hF x) (hm x) hγ hγU)
  have hind (k : ℕ) : edist (γ 0) (γ (t k)) ≤ g.pathELength γ 0 (t k) := by
    induction k with
    | zero =>
        rw [ht0]
        change edist (γ 0) (γ 0) ≤ _
        rw [edist_self]
        exact bot_le
    | succ k ih =>
        calc
          edist (γ 0) (γ (t (k + 1))) ≤
              edist (γ 0) (γ (t k)) + edist (γ (t k)) (γ (t (k + 1))) :=
            edist_triangle _ _ _
          _ ≤ g.pathELength γ 0 (t k) + g.pathELength γ (t k) (t (k + 1)) :=
            add_le_add ih (hstep k)
          _ = g.pathELength γ 0 (t (k + 1)) := by
            let : Bundle.RiemannianBundle
                (TangentSpace (𝓡 (n + 1)) : AsymptoticConePositive p hc → Type _) :=
              ⟨g.toRiemannianMetric⟩
            exact Manifold.pathELength_add (I := 𝓡 (n + 1)) (γ := γ)
              (t k).property.1 (htmono (Nat.le_succ k))
  have hfinal := hind N
  rw [hN N le_rfl] at hfinal
  exact hfinal



theorem positiveCone_edist_le_metric_edist :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ x y : AsymptoticConePositive p hc,
      edist x y ≤ (positiveConeMetric hne hcover).edist x y := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro x y
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (n + 1)) : AsymptoticConePositive p hc → Type _) :=
    ⟨(positiveConeMetric hne hcover).toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      (I := 𝓡 (n + 1)) hr zero_lt_one
  have hle := positiveCone_edist_le_pathELength hne hcover γ hγ
  rw [h0, h1] at hle
  exact hle.trans_lt hlen



theorem UnitSliceRadialChartData.positiveChart_symm_inner
    (d : UnitSliceRadialChartData hc n) :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ x ∈ (d.positiveChart hne).target, ∀ v w,
      d.metric.inner x v w = (positiveConeMetric hne hcover).inner
        ((d.positiveChart hne).symm x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (d.positiveChart hne).symm x v)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (d.positiveChart hne).symm x w) := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro x hx v w
  let y : d.source := ⟨x, by
    change x ∈ d.ambientChart.source
    rwa [d.positiveChart_target hne] at hx⟩
  have hmax : d.positiveChart hne ∈ maximalAtlas (𝓡 (n + 1)) ∞
      (AsymptoticConePositive p hc) := subset_maximalAtlas ⟨d, rfl⟩
  have hdiff := ((contMDiffOn_symm_of_mem_maximalAtlas hmax).contMDiffAt
    ((d.positiveChart hne).open_target.mem_nhds hx)).mdifferentiableAt (by simp)
  have hfun : (fun z : d.source => (d.positiveChart hne).symm z) = d.positiveMap := by
    funext z
    exact (d.positiveMap_eq_chart_symm hne z).symm
  have hderiv := mfderiv_opens_restrict d.source (d.positiveChart hne).symm
    (x := y) hdiff
  rw [hfun] at hderiv
  have hm := positiveConeMetric_inner hne hcover d y v w
  rw [d.positiveMap_eq_chart_symm hne y, hderiv] at hm
  exact hm




theorem exists_positiveCone_local_metric_edist_eq :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ a : AsymptoticConePositive p hc,
      ∃ U : Set (AsymptoticConePositive p hc), IsOpen U ∧ a ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, (positiveConeMetric hne hcover).edist y z = edist y z := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  obtain ⟨d, ha⟩ := positiveCone_radialAtlas_covers hc n hne hcover a
  let C := d.positiveChart hne
  let g := positiveConeMetric hne hcover
  have hmax : C ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d, rfl⟩
  have hC := contMDiffOn_symm_of_mem_maximalAtlas hmax
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (n + 1)) : UnitSliceAmbient n → Type _) :=
    ⟨d.metric.toRiemannianMetric⟩
  have hcomm (u v : UnitSliceAmbient n) : d.metric.edist u v = d.metric.edist v u :=
    Manifold.riemannianEDist_comm
  let metricE : MetricSpace (UnitSliceAmbient n) := d.metric.toMetricSpace
  let : MetricSpace (UnitSliceAmbient n) := metricE
  let : PseudoMetricSpace (UnitSliceAmbient n) := metricE.toPseudoMetricSpace
  let : PseudoEMetricSpace (UnitSliceAmbient n) := metricE.toPseudoMetricSpace.toPseudoEMetricSpace
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (C.open_target.mem_nhds (C.map_source ha))
  let U := C.source ∩ C ⁻¹' Metric.ball (C a) (R / 4)
  refine ⟨U, C.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨ha, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  intro y hy z hz
  apply le_antisymm _ (positiveCone_edist_le_metric_edist hne hcover y z)
  have hyC := C.map_source hy.1
  have hzC := C.map_source hz.1
  have hd : edist y z = d.metric.edist (C y) (C z) := by
    have hh := d.positiveChart_symm_distance hne hyC hzC
    rw [C.left_inv hy.1, C.left_inv hz.1] at hh
    rw [edist_dist, hh, ENNReal.ofReal_toReal (d.metric.edist_ne_top _ _)]
  rw [hd]
  apply le_of_forall_gt
  intro l hl
  have hsmall : d.metric.edist (C y) (C z) < ENNReal.ofReal (R / 2) := by
    have hy' : (d.metric.edist (C y) (C a)).toReal < R / 4 := hy.2
    have hz' : (d.metric.edist (C z) (C a)).toReal < R / 4 := hz.2
    have ht := d.metric.toReal_edist_triangle (C y) (C a) (C z)
    rw [hcomm (C a) (C z)] at ht
    have hh : (d.metric.edist (C y) (C z)).toReal < R / 2 := by linarith
    rw [← ENNReal.ofReal_toReal (d.metric.edist_ne_top (C y) (C z))]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hh
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      (I := 𝓡 (n + 1)) (lt_min hl hsmall) zero_lt_one
  have hγC : MapsTo γ (Icc (0 : ℝ) 1) C.target := by
    intro t ht
    apply hball
    have hinit := d.metric.edist_le_pathELength_of_mem_Icc hγ.contMDiffOn ht
    rw [h0] at hinit
    have hnear : d.metric.edist (C y) (γ t) < ENNReal.ofReal (R / 2) :=
      hinit.trans_lt (hlen.trans_le (min_le_right _ _))
    have hnear' : (d.metric.edist (C y) (γ t)).toReal < R / 2 := by
      exact ENNReal.toReal_lt_of_lt_ofReal hnear
    have hy' : (d.metric.edist (C y) (C a)).toReal < R / 4 := hy.2
    have ht' := d.metric.toReal_edist_triangle (γ t) (C y) (C a)
    rw [hcomm (γ t) (C y)] at ht'
    change (d.metric.edist (γ t) (C a)).toReal < R
    linarith
  have hm := d.positiveChart_symm_inner hne hcover
  have heq := positive_pathELength_comp_eq_on d.metric g C.open_target hC hm hγ hγC
  have hmap : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1
      (C.symm ∘ γ) (Icc (0 : ℝ) 1) :=
    (hC.of_le (by simp)).comp hγ.contMDiffOn hγC
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (n + 1)) : AsymptoticConePositive p hc → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpath := Manifold.riemannianEDist_le_pathELength (I := 𝓡 (n + 1))
    hmap (by simpa only [Function.comp_apply, h0] using C.left_inv hy.1)
    (by simpa only [Function.comp_apply, h1] using C.left_inv hz.1) zero_le_one
  exact (hpath.trans_eq heq).trans_lt (hlen.trans_le (min_le_left _ _))



theorem positiveCone_metric_edist_le_of_lipschitz_path :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ (γ : unitInterval → AsymptoticConePositive p hc) (L : ℝ≥0),
      LipschitzWith L γ → (positiveConeMetric hne hcover).edist (γ 0) (γ 1) ≤ L := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro γ L hγ
  let g := positiveConeMetric hne hcover
  choose U hU hx hd using exists_positiveCone_local_metric_edist_eq hne hcover
  let c := fun x => γ ⁻¹' U x
  have hcopen : ∀ x, IsOpen (c x) := fun x => (hU x).preimage hγ.continuous
  have hccover : univ ⊆ ⋃ x, c x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, hx (γ t)⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover
  have hstep (k : ℕ) : g.edist (γ (t k)) (γ (t (k + 1))) ≤
      ENNReal.ofReal ((L : ℝ) * ((t (k + 1) : ℝ) - t k)) := by
    obtain ⟨x, htx⟩ := hsub k
    have htime := htmono (Nat.le_succ k)
    rw [hd x _ (htx ⟨le_rfl, htime⟩) _ (htx ⟨htime, le_rfl⟩), edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h := hγ.dist_le_mul (t k) (t (k + 1))
    change dist (γ (t k)) (γ (t (k + 1))) ≤ (L : ℝ) * |(t k : ℝ) - t (k + 1)| at h
    rw [abs_of_nonpos (sub_nonpos.mpr (show (t k : ℝ) ≤ t (k + 1) from htime))] at h
    simpa only [neg_sub] using h
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (n + 1)) : AsymptoticConePositive p hc → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hind (k : ℕ) : g.edist (γ 0) (γ (t k)) ≤
      ENNReal.ofReal ((L : ℝ) * (t k : ℝ)) := by
    induction k with
    | zero =>
        rw [ht0]
        exact (show g.edist (γ 0) (γ 0) = 0 from Manifold.riemannianEDist_self).le.trans bot_le
    | succ k ih =>
        calc
          g.edist (γ 0) (γ (t (k + 1))) ≤
              g.edist (γ 0) (γ (t k)) + g.edist (γ (t k)) (γ (t (k + 1))) :=
            Manifold.riemannianEDist_triangle
          _ ≤ ENNReal.ofReal ((L : ℝ) * (t k : ℝ)) +
              ENNReal.ofReal ((L : ℝ) * ((t (k + 1) : ℝ) - t k)) :=
            add_le_add ih (hstep k)
          _ = ENNReal.ofReal ((L : ℝ) * (t (k + 1) : ℝ)) := by
            rw [← ENNReal.ofReal_add (mul_nonneg L.coe_nonneg (t k).property.1)
              (mul_nonneg L.coe_nonneg (sub_nonneg.mpr (htmono (Nat.le_succ k))))]
            congr 1
            ring
  have hfinal := hind N
  rw [hN N le_rfl] at hfinal
  simpa using hfinal



theorem positiveCone_metric_edist_eq_of_metric_segment :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ (x y : AsymptoticConePositive p hc)
      (γ : ℝ → AsymptoticCone p hc), γ 0 = x.1 → γ 1 = y.1 →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y) →
      dist x y < (asymptoticConeRadius hc x.1 : ℝ) + asymptoticConeRadius hc y.1 →
      (positiveConeMetric hne hcover).edist x y = edist x y := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro x y γ h0 h1 hγ hstrict
  have hzero (z : AsymptoticCone p hc) (hz : asymptoticConeRadius hc z = 0)
      (w : AsymptoticCone p hc) : dist w z = asymptoticConeRadius hc w := by
    obtain ⟨⟨r, u⟩, rfl⟩ := surjective_asymptoticConeProjection hc z
    rw [asymptoticConeRadius_projection] at hz
    change r = 0 at hz
    subst r
    obtain ⟨⟨s, v⟩, rfl⟩ := surjective_asymptoticConeProjection hc w
    exact dist_asymptoticConeProjection_zero hc s v u
  have hpos (t : unitInterval) : 0 < asymptoticConeRadius hc (γ t) := by
    by_contra h
    have hz : asymptoticConeRadius hc (γ t) = 0 := le_antisymm (le_of_not_gt h) bot_le
    have hleft := hγ 0 (by simp) t t.property
    have hright := hγ t t.property 1 (by simp)
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.property.1, hzero _ hz x.1] at hleft
    rw [h1, abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub,
      dist_comm, hzero _ hz y.1] at hright
    nlinarith
  let P : unitInterval → AsymptoticConePositive p hc := fun t => ⟨γ t, hpos t⟩
  have hP : LipschitzWith (nndist x y) P := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change dist (γ s) (γ t) ≤ dist x y * |(s : ℝ) - t|
    rw [hγ s s.property t t.property, mul_comm]
  have hbound := positiveCone_metric_edist_le_of_lipschitz_path hne hcover P (nndist x y) hP
  have hP0 : P 0 = x := Subtype.ext h0
  have hP1 : P 1 = y := Subtype.ext h1
  rw [hP0, hP1] at hbound
  exact le_antisymm (by simpa only [edist_nndist] using hbound)
    (positiveCone_edist_le_metric_edist hne hcover x y)

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

private theorem exists_distinct_nearby_chart_point
    {k : ℕ} (hk : 1 ≤ k) {S : Type*} [MetricSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) S] (x : S) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : S, y ≠ x ∧ dist x y < ε := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let : PerfectSpace (EuclideanSpace ℝ (Fin k)) := perfectSpace_of_module ℝ _
  let e := chartAt (EuclideanSpace ℝ (Fin k)) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hxe : e x ∈ e.target := e.map_source hx
  have hball : e.symm ⁻¹' Metric.ball x ε ∈ 𝓝 (e x) := by
    apply (e.continuousAt_symm hxe).preimage_mem_nhds
    simpa only [e.left_inv hx] using Metric.ball_mem_nhds x hε
  obtain ⟨u, hu, hune⟩ := nhdsWithin_neBot.mp
    (inferInstance : NeBot (𝓝[≠] (e x)))
    (inter_mem (e.open_target.mem_nhds hxe) hball)
  have hneq : u ≠ e x := by simpa using hune
  refine ⟨e.symm u, ?_, ?_⟩
  · intro h
    exact hneq ((e.right_inv hu.1).symm.trans (congrArg e h))
  · simpa only [mem_preimage, Metric.mem_ball, dist_comm] using hu.2






theorem positiveConeMetric_edist_eq
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (g : RiemannianMetric m M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) (hk : 1 ≤ k) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ (hne : Nonempty (AsymptoticConePositive p hc))
      (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
        ∃ (d : UnitSliceRadialChartData hc k) (x : d.Level), (d.levelHomeomorph x).1 = z),
    letI := positiveConeChartedSpace hc k hne hcover
    letI := positiveCone_isManifold hc k hne hcover
    ∀ x y : AsymptoticConePositive p hc,
      (positiveConeMetric hne hcover).edist x y = EDist.edist x y := by
  let := g.toMetricSpace
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  dsimp only
  intro hne hcover
  let := positiveConeChartedSpace hc k hne hcover
  let := positiveCone_isManifold hc k hne hcover
  let := unitSliceChartedSpace hc k hcover
  let gP := positiveConeMetric hne hcover
  let P := asymptoticConePositiveProjection hc
  have hpair (r s : Ioi (0 : ℝ≥0)) (u v : AsymptoticLink p hc) (huv : dist u v < 2) :
      gP.edist (P (r, u)) (P (s, v)) = EDist.edist (P (r, u)) (P (s, v)) := by
    obtain ⟨γ, h0, h1, hγ⟩ :=
      g.exists_asymptoticCone_metric_segment D hcomplete hsec p (P (r, u)).1 (P (s, v)).1
    apply positiveCone_metric_edist_eq_of_metric_segment hne hcover _ _ γ h0 h1 hγ
    change dist (asymptoticConeProjection hc (r.1, u))
      (asymptoticConeProjection hc (s.1, v)) < (r.1 : ℝ) + s.1
    rw [dist_asymptoticConeProjection]
    have hr : (0 : ℝ) < r.1 := r.property
    have hs : (0 : ℝ) < s.1 := s.property
    apply (Real.sqrt_lt' (add_pos hr hs)).mpr
    have hsq : dist u v ^ 2 < 4 := by nlinarith [dist_nonneg (x := u) (y := v)]
    have hmul := mul_lt_mul_of_pos_left hsq (mul_pos hr hs)
    dsimp only
    nlinarith
  intro x y
  obtain ⟨⟨r, u⟩, rfl⟩ := (asymptoticConePositiveHomeomorph hc).surjective x
  obtain ⟨⟨s, v⟩, rfl⟩ := (asymptoticConePositiveHomeomorph hc).surjective y
  change gP.edist (P (r, u)) (P (s, v)) = EDist.edist (P (r, u)) (P (s, v))
  by_cases huv : dist u v < 2
  · exact hpair r s u v huv
  let e := asymptoticConeUnitIsometry hc
  have huvle : dist u v ≤ 2 := by
    simpa only [e.isometry.dist_eq] using asymptoticConeUnitSlice_dist_le_two hc (e u) (e v)
  have huveq : dist u v = 2 := le_antisymm huvle (le_of_not_gt huv)
  have hnear (j : ℕ) : ∃ w : AsymptoticLink p hc,
      w ≠ v ∧ dist v w < 1 / ((j : ℝ) + 1) := by
    obtain ⟨z, hzne, hdist⟩ := exists_distinct_nearby_chart_point hk (e v)
      (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    refine ⟨e.symm z, ?_, ?_⟩
    · intro h
      exact hzne ((e.apply_symm_apply z).symm.trans (congrArg e h))
    · simpa only [← e.isometry.dist_eq, e.apply_symm_apply] using hdist
  choose w hwne hwdist using hnear
  have hwt : Tendsto w atTop (𝓝 v) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun j => by simpa only [dist_comm] using (hwdist j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hwstrict (j : ℕ) : dist u (w j) < 2 := by
    have hb := g.asymptoticLink_dist_sq_add_le_four_of_antipodal
      D hcomplete hsec p u v (w j) huveq
    have hp : 0 < dist v (w j) := dist_pos.mpr (hwne j).symm
    nlinarith [dist_nonneg (x := u) (y := w j)]
  have hPt : Tendsto (fun j => P (s, w j)) atTop (𝓝 (P (s, v))) :=
    (continuous_asymptoticConePositiveProjection hc).continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds hwt)
  have hcont : Continuous (fun z => gP.edist (P (r, u)) z) := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 (k + 1)) : AsymptoticConePositive p hc → Type _) :=
      ⟨gP.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (k + 1)))
        (TangentSpace (𝓡 (k + 1)) : AsymptoticConePositive p hc → Type _) :=
      ⟨⟨gP.inner, gP.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let em : EMetricSpace (AsymptoticConePositive p hc) :=
      EMetricSpace.ofRiemannianMetric (𝓡 (k + 1)) (AsymptoticConePositive p hc)
    let : EMetricSpace (AsymptoticConePositive p hc) := em
    let : PseudoEMetricSpace (AsymptoticConePositive p hc) := em.toPseudoEMetricSpace
    let : EDist (AsymptoticConePositive p hc) := em.toPseudoEMetricSpace.toEDist
    change Continuous (fun z : AsymptoticConePositive p hc => EDist.edist (P (r, u)) z)
    exact continuous_const.edist continuous_id
  have hleft : Tendsto (fun j => gP.edist (P (r, u)) (P (s, w j)))
      atTop (𝓝 (gP.edist (P (r, u)) (P (s, v)))) :=
    hcont.continuousAt.tendsto.comp hPt
  have hright : Tendsto (fun j => EDist.edist (P (r, u)) (P (s, w j)))
      atTop (𝓝 (EDist.edist (P (r, u)) (P (s, v)))) := tendsto_const_nhds.edist hPt
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun j => (hpair r s u (w j) (hwstrict j)).symm))

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio




theorem positiveConeMetric_edist_eq_of_zero_ratio
    {n : ℕ} (hn : 1 ≤ n) {M : Type u} [TopologicalSpace M] [T3Space M]
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
    ∀ x y : AsymptoticConePositive p hc,
      (positiveConeMetric hne hcover).edist x y = EDist.edist x y := by
  let := (F.metric t₀).toMetricSpace
  dsimp only
  exact (F.metric t₀).positiveConeMetric_edist_eq (F.connection t₀) (hcomplete t₀ ht₀)
    (fun x v w => (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w) p hn _ _

end PoincareConjecture.RicciFlow
