import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.RadialCurve











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem exists_geodesic_to_time (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ∃ S : Set ℝ, IsOpen S ∧ Convex ℝ S ∧ 0 ∈ S ∧ t ∈ S ∧
      ∃ γ : ℝ → M, g.IsGeodesicOn γ S ∧ γ 0 = p ∧
        HasDerivAt (fun r => extChartAt (𝓡 n) p (γ r)) v 0 := by
  by_cases ht : t = 0
  · subst t
    obtain ⟨δ, hδ, _, γ, hγ, hp, hv⟩ := g.exists_geodesic_initial_data p v
    have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    exact ⟨Ioo (-δ) δ, isOpen_Ioo, convex_Ioo _ _, h0, h0, γ, hγ, hp, hv⟩
  let speed := Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
    (extChartAt (𝓡 n) p p) (t • v) (t • v))
  have hspeed : 0 ≤ speed := Real.sqrt_nonneg _
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hcompact : IsCompact (closure (g.ball p (speed + 1))) := by
    apply (g.isCompact_closedBall_of_metricComplete hc p (speed + 1)).of_isClosed_subset
      isClosed_closure
    apply closure_minimal (fun q (h : g.edist p q < ENNReal.ofReal (speed + 1)) => h.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  obtain ⟨ε, hε, γ, hγ, hp, hv, _⟩ :=
    g.exists_geodesic_through_one_of_precompact_ball p
      (show 0 < speed + 1 by linarith) hcompact (t • v) (by dsimp [speed]; linarith)
  let S := (fun r : ℝ => t⁻¹ * r) ⁻¹' Ioo (-ε) (1 + ε)
  have hS : IsOpen S := isOpen_Ioo.preimage (by fun_prop)
  have hconv : Convex ℝ S := (convex_Ioo (-ε) (1 + ε)).smul_preimage t⁻¹
  have h0 : (0 : ℝ) ∈ S := by dsimp [S]; constructor <;> linarith
  have htS : t ∈ S := by
    change t⁻¹ * t ∈ Ioo (-ε) (1 + ε)
    rw [inv_mul_cancel₀ ht]
    constructor <;> linarith
  refine ⟨S, hS, hconv, h0, htS, (fun r => γ (t⁻¹ * r)), hγ.comp_mul t⁻¹,
    by simpa using hp, ?_⟩
  have hv' : HasDerivAt (fun r => extChartAt (𝓡 n) p (γ r)) (t • v) (t⁻¹ * 0) := by
    simpa using hv
  simpa only [Function.comp_def, id_eq, mul_one, smul_smul, inv_mul_cancel₀ ht, one_smul]
    using hv'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t⁻¹)



theorem exists_global_geodesic (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ γ : ℝ → M, g.IsGeodesicOn γ univ ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 := by
  classical
  choose S hSo hSc hS0 hSt f hfg hf0 hfd using exists_geodesic_to_time g hc p v
  have hcompat (a b : ℝ) : EqOn (f a) (f b) (S a ∩ S b) := by
    have hfa : g.IsGeodesicOn (f a) (S a ∩ S b) := fun t ht => hfg a t ht.1
    have hfb : g.IsGeodesicOn (f b) (S a ∩ S b) := fun t ht => hfg b t ht.2
    have heq := hfa.eq_nhds_on_of_initial_data hfb ((hSc a).inter (hSc b)).isPreconnected
      ⟨hS0 a, hS0 b⟩ p (by rw [hf0]; exact mem_extChartAt_source p)
      ((hf0 a).trans (hf0 b).symm) ((hfd a).deriv.trans (hfd b).deriv.symm)
    exact fun t ht => (heq t ht).self_of_nhds
  let Γ : ℝ → M := fun t => f t t
  have hgerm (t : ℝ) : Γ =ᶠ[𝓝 t] f t := by
    filter_upwards [(hSo t).mem_nhds (hSt t)] with u hu
    exact hcompat u t ⟨hSt u, hu⟩
  refine ⟨Γ, ?_, hf0 0, (hfd 0).congr_of_eventuallyEq
    ((hgerm 0).fun_comp (extChartAt (𝓡 n) p))⟩
  intro t _
  obtain ⟨q, a, w, hlocal⟩ := hfg t t (hSt t)
  refine ⟨q, a, w, ?_⟩
  filter_upwards [hlocal, hgerm t] with u hu heq
  exact ⟨heq.trans hu.1, hu.2⟩



theorem contMDiff_global_geodesic {g : RiemannianMetric n M}
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ := by
  intro t
  let p := γ t
  let v := deriv (fun u => extChartAt (𝓡 n) p (γ u)) t
  obtain ⟨V, δ, Φ, hV, hz, _, hδ, hΦ, hinit, hflow⟩ :=
    g.exists_smooth_chart_geodesic_flow p v
  let z := (extChartAt (𝓡 n) p p, v)
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have heq := hγ.eq_nhds_chart_flow (convex_univ : Convex ℝ (univ : Set ℝ)) p hδ
    (fun u hu => ⟨(hflow z hz u hu).1, (hflow z hz u hu).2.1⟩)
    (a := t) (b := t) (mem_univ t) (mem_univ t) (mem_extChartAt_source p)
    (hinit z hz) (by simpa only [sub_self] using h0)
  have hread : ContDiffAt ℝ ∞ (fun u : ℝ => Φ (z, u - t)) t := by
    have hΦ0 : ContDiffAt ℝ ∞ Φ (z, t - t) :=
      hΦ.contDiffAt ((hV.prod isOpen_Ioo).mem_nhds (by
        simpa only [sub_self] using
          (show (z, (0 : ℝ)) ∈ V ×ˢ Ioo (-δ) δ from ⟨hz, h0⟩)))
    have htime : ContDiffAt ℝ ∞ (fun u : ℝ => (z, u - t)) t :=
      contDiffAt_const.prodMk (contDiffAt_id.sub contDiffAt_const)
    simpa only [Function.comp_def] using hΦ0.comp t htime
  have htarget : (Φ (z, t - t)).1 ∈ (extChartAt (𝓡 n) p).target := by
    simpa only [sub_self] using (hflow z hz 0 h0).1
  have hsmooth := ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htarget)).comp t
      (contMDiffAt_iff_contDiffAt.mpr hread.fst)
  exact hsmooth.congr_of_eventuallyEq heq

end PoincareConjecture.RiemannianMetric
