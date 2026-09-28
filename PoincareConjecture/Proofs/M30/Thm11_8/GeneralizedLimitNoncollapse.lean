import PoincareConjecture.Proofs.M30.Thm11_8.RecenteredNormalizedVolume
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedPointNoncollapse
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCurvatureConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedBallVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem generalized_limit_noncollapsed_of_longSlabService
    {S : GeneralizedBlowupSequence.{u}} {T0 : ℝ≥0∞} {kappa r0 : ℝ}
    (G : GeneralizedBlowupConvergence S (blowupBackwardInterval T0))
    (H : M30LongSlabControlService S kappa r0 T0)
    (hr0 : 0 < r0) :
    BlowupLimitNoncollapsed G.limit kappa := by
  intro t ht p r hr htime hcurv
  obtain ⟨N, hNt⟩ := exists_generalized_time_shift G ht
  apply generalized_limit_ball_volume_lower_bound G ht N hNt p hr kappa
  intro rho hrho hrhor
  obtain ⟨a, hrhoa, har⟩ := exists_between hrhor
  obtain ⟨b, hab, hbr⟩ := exists_between har
  have ha : 0 < a := hrho.trans hrhoa
  have hb : 0 < b := ha.trans hab
  let g := G.limit.flow.metric t
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  let K := closure (g.ball p b)
  have hKclosed : K ⊆ {x | g.edist p x ≤ ENNReal.ofReal b} := by
    apply closure_minimal
      (fun x (hx : g.edist p x < ENNReal.ofReal b) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hK : IsCompact K := IsCompact.of_isClosed_subset
    (g.isCompact_closedBall_of_metricComplete (G.limit.complete t ht) p b)
    isClosed_closure hKclosed
  have hKr : K ⊆ g.ball p r := fun x hx =>
    (hKclosed hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hbr)
  have haK : g.ball p a ⊆ K := by
    intro x hx
    exact subset_closure (hx.trans_le (ENNReal.ofReal_le_ofReal hab.le))
  let I := Icc (t - rho ^ 2) t
  have hsq : rho ^ 2 < r ^ 2 := (sq_lt_sq₀ hrho.le hr.le).mpr hrhor
  have hITest : I ⊆ Ioc (t - r ^ 2) t := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hIJ : I ⊆ blowupBackwardInterval T0 := hITest.trans htime
  have hdelta : 0 < rho⁻¹ ^ 2 - r⁻¹ ^ 2 := by
    apply sub_pos.mpr
    rw [inv_pow, inv_pow]
    exact (inv_lt_inv₀ (sq_pos_of_pos hr) (sq_pos_of_pos hrho)).mpr hsq
  let C := a / rho
  have hC : 1 < C := (one_lt_div hrho).mpr hrhoa
  have hCrho : C * rho = a := div_mul_cancel₀ a hrho.ne'
  have herror := (tendsto_add_atTop_nat N).eventually
    (eventually_generalized_curvature_error G (I := I) isCompact_Icc hIJ hK hdelta)
  have hpoint := (tendsto_add_atTop_nat N).eventually
    (eventually_generalized_point_noncollapsed_of_longSlabService G H ht p)
  have hlarge := (S.scalar_diverges.comp
    (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N))).eventually_ge_atTop
      ((rho / r0) ^ 2)
  filter_upwards [eventually_generalized_tangent_comparison G ht N hNt hK hC,
    herror, hpoint, hlarge] with k hcompare herr hnon hscale
  let e := generalizedSliceHomeomorph G (k + N) t (hNt k)
  let h := normalizedBlowupSliceMetric S (G.subsequence (k + N)) t
  have he : e.MDifferentiable (𝓡 3) (𝓡 3) := by
    constructor
    · intro x hx
      exact ((generalizedSliceHomeomorph_contMDiffAt G (k + N) t (hNt k) hx).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
    · intro y hy
      exact ((generalizedSliceHomeomorph_symm_contMDiffAt G (k + N) t (hNt k) hy).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hinverse := g.inverse_tangentNorm_le_of_le h e he hcompare.1
    (fun x hx v => (hcompare.2 x hx v).2)
  have hcapture : h.ball (e p) rho ⊆ e '' g.ball p a := by
    have hh := g.ball_subset_image_ball_of_inverse_tangentNorm_le h e p hb
      (zero_lt_one.trans hC) (hCrho.trans_lt hab) hK hcompare.1
      (fun y hy => (generalizedSliceHomeomorph_symm_contMDiffAt G (k + N) t (hNt k) hy).of_le
        (by simp)) hinverse
    simpa only [hCrho] using hh
  have hsqrt : 0 < Real.sqrt (S.scale (G.subsequence (k + N))) :=
    Real.sqrt_pos.mpr (S.base_scalar_pos (G.subsequence (k + N)))
  have hcutoff : rho / Real.sqrt (S.scale (G.subsequence (k + N))) ≤ r0 := by
    apply (div_le_iff₀ hsqrt).mpr
    have hh := (div_le_iff₀ hr0).mp (Real.le_sqrt_of_sq_le hscale)
    simpa only [GeneralizedBlowupSequence.scale, Function.comp_apply, mul_comm] using hh
  let W : SpacetimeInterval := {
    domain := Icc (-G.exhaustion.time (k + N)) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-G.exhaustion.time (k + N),
      ⟨le_rfl, neg_nonpos.mpr (G.exhaustion.time_pos (k + N)).le⟩,
      0, ⟨neg_nonpos.mpr (G.exhaustion.time_pos (k + N)).le, le_rfl⟩,
      (neg_lt_zero.mpr (G.exhaustion.time_pos (k + N))).ne⟩ }
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space (k + N), G.exhaustion.space_open (k + N)⟩
  have hback : Icc (-rho ^ 2) 0 ⊆ (fun s : ℝ => t + s) ⁻¹' W.domain := by
    intro s hs
    apply herr.1
    constructor <;> linarith [hs.1, hs.2]
  have hball : h.ball (e p) rho ⊆
      (G.embedding (k + N)).forward t (hNt k) '' G.exhaustion.space (k + N) :=
    hcapture.trans (image_mono (haK.trans hcompare.1))
  have htest : ∀ s (hs : s ∈ Ioc (-rho ^ 2) 0), ∀ y ∈ h.ball (e p) rho,
      |(S.flow (G.subsequence (k + N))).curvatureNorm
        ((G.embedding (k + N)).pointMap (t + s)
          (hback (Ioc_subset_Icc_self hs)) ((G.embedding (k + N)).inverse t (hNt k) y))| /
        S.scale (G.subsequence (k + N)) ≤ rho⁻¹ ^ 2 := by
    intro s hs y hy
    obtain ⟨x, hx, hxy⟩ := hcapture hy
    have hxK := haK hx
    have hinv : (G.embedding (k + N)).inverse t (hNt k) y = x := by
      change e.symm y = x
      rw [← hxy, e.left_inv (hcompare.1 hxK)]
    have hts : t + s ∈ I := by constructor <;> linarith [hs.1, hs.2]
    have hbound := hcurv (t + s) (hITest hts) x (hKr hxK)
    have hclose := (abs_lt.mp (herr.2.2 (t + s) hts
      (hback (Ioc_subset_Icc_self hs)) x hxK)).2
    rw [hinv]
    have hnorm : 0 ≤ (S.flow (G.subsequence (k + N))).curvatureNorm
        ((G.embedding (k + N)).pointMap (t + s) (hback (Ioc_subset_Icc_self hs)) x) :=
      Real.sqrt_nonneg _
    rw [abs_of_nonneg hnorm]
    have htarget := (le_abs_self _).trans hbound
    linarith
  exact Cylinder.normalized_volume_of_recentered_noncollapse
    (J := W) (U := U) (G.embedding (k + N)) ⟨t, hNt k⟩ (e p)
    hrho hcutoff hback (hnon (hNt k)) hball htest

end PoincareConjecture.M30
