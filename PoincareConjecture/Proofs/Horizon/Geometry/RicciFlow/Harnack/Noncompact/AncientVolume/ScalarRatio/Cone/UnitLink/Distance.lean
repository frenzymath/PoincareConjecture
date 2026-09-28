import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Topology.UnitInterval

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hc : RayComparison p} {n : ℕ}

theorem exists_unitSlice_local_ambient_realization
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (U : Set (AsymptoticConeUnitSlice p hc)), IsOpen U ∧ x ∈ U ∧
        ∃ (h : RiemannianMetric (n + 1) (UnitSliceAmbient n))
          (F : AsymptoticConeUnitSlice p hc → UnitSliceAmbient n),
          ContMDiffOn (𝓡 n) (𝓡 (n + 1)) ∞ F U ∧
          (∀ y ∈ U, ∀ v w,
            (unitSliceMetric hcover).inner y v w = h.inner (F y)
              (mfderiv (𝓡 n) (𝓡 (n + 1)) F y v)
              (mfderiv (𝓡 n) (𝓡 (n + 1)) F y w)) ∧
          ∀ y ∈ U, ∀ z ∈ U, edist y z = h.edist (F y) (F z) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro x
  obtain ⟨d, z₀, rfl⟩ := hcover x
  let q : d.Level → AsymptoticConeUnitSlice p hc := fun z => (d.levelHomeomorph z).1
  have hq := d.isLocalDiffeomorph_levelMap hc n hcover
  let e := (hq z₀).localInverse
  let incl := openLevelIncl d.potential d.source (1 / 2)
  have hi : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ incl :=
    contMDiff_openLevelIncl d.smooth d.source d.regular n (1 / 2)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := e.contMDiffOn
  have hright (y : AsymptoticConeUnitSlice p hc) (hy : y ∈ e.source) : q (e y) = y :=
    (hq z₀).localInverse_right_inv hy
  refine ⟨e.source, e.open_source, (hq z₀).localInverse_mem_source,
    d.metric, incl ∘ e, hi.comp_contMDiffOn he, ?_, ?_⟩
  · intro y hy v w
    have hediff := e.mdifferentiableAt (by simp) hy
    have hcomp : (mfderiv (𝓡 n) (𝓡 n) q (e y)).comp
        (mfderiv (𝓡 n) (𝓡 n) e y) = ContinuousLinearMap.id ℝ _ := by
      rw [← mfderiv_comp y (hq.mdifferentiable (by simp) (e y)) hediff]
      have hgerm : q ∘ e =ᶠ[𝓝 y] id :=
        Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) hright
      rw [hgerm.mfderiv_eq, mfderiv_id]
    have hm := unitSliceMetric_inner hcover d (e y)
      (mfderiv (𝓡 n) (𝓡 n) e y v) (mfderiv (𝓡 n) (𝓡 n) e y w)
    have hv : mfderiv (𝓡 n) (𝓡 n) q (e y) (mfderiv (𝓡 n) (𝓡 n) e y v) = v :=
      congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A v) hcomp
    have hw : mfderiv (𝓡 n) (𝓡 n) q (e y) (mfderiv (𝓡 n) (𝓡 n) e y w) = w :=
      congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A w) hcomp
    change d.levelMetric.inner (e y) _ _ = (unitSliceMetric hcover).inner (q (e y))
      (mfderiv (𝓡 n) (𝓡 n) q (e y) (mfderiv (𝓡 n) (𝓡 n) e y v))
      (mfderiv (𝓡 n) (𝓡 n) q (e y) (mfderiv (𝓡 n) (𝓡 n) e y w)) at hm
    rw [hv, hw, hright y hy] at hm
    rw [← hm, mfderiv_comp y (hi.mdifferentiable (by simp) (e y)) hediff]
    rfl
  · intro y hy z hz
    have heq : dist y z = (d.metric.edist (incl (e y)) (incl (e z))).toReal := by
      calc
        dist y z = dist (q (e y)) (q (e z)) := by rw [hright y hy, hright z hz]
        _ = _ := by
          change dist (q (e y)).1 (q (e z)).1 = _
          rw [d.levelHomeomorph_val, d.levelHomeomorph_val]
          exact d.distance _ (e y).1.property _ (e z).1.property
    rw [edist_dist, heq, ENNReal.ofReal_toReal (d.metric.edist_ne_top _ _)]
    rfl

private theorem pathELength_comp_eq_on
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

theorem unitSlice_edist_le_pathELength
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ γ : ℝ → AsymptoticConeUnitSlice p hc,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ →
      edist (γ 0) (γ 1) ≤ (unitSliceMetric hcover).pathELength γ 0 1 := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro γ hγ
  let g := unitSliceMetric hcover
  choose U hU hx h F hF hm hd using exists_unitSlice_local_ambient_realization hcover
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
      (pathELength_comp_eq_on g (h x) (hU x) (hF x) (hm x) hγ hγU)
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
                (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) :=
              ⟨g.toRiemannianMetric⟩
            exact Manifold.pathELength_add (I := 𝓡 n) (γ := γ)
              (t k).property.1 (htmono (Nat.le_succ k))
  have hfinal := hind N
  rw [hN N le_rfl] at hfinal
  exact hfinal

theorem unitSlice_edist_le_metric_edist
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x y : AsymptoticConeUnitSlice p hc,
      edist x y ≤ (unitSliceMetric hcover).edist x y := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro x y
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) :=
    ⟨(unitSliceMetric hcover).toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := 𝓡 n) hr zero_lt_one
  have hle := unitSlice_edist_le_pathELength hcover γ hγ
  rw [h0, h1] at hle
  exact hle.trans_lt hlen

theorem unitSlice_dist_le_metric_toReal_edist
    [PreconnectedSpace (AsymptoticConeUnitSlice p hc)]
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x y : AsymptoticConeUnitSlice p hc,
      dist x y ≤ ((unitSliceMetric hcover).edist x y).toReal := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro x y
  have h := ENNReal.toReal_mono ((unitSliceMetric hcover).edist_ne_top x y)
    (unitSlice_edist_le_metric_edist hcover x y)
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h

end Poincare.AncientVolume.ScalarRatio
