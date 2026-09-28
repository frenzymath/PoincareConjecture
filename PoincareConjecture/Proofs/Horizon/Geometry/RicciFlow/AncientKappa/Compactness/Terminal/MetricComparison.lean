import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactMetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.PartialCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TerminalConvergence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1000000
set_option maxSynthPendingDepth 32

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {N : ℕ → Type*} [∀ k, TopologicalSpace (N k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (N k)]
  [∀ k, IsManifold (𝓡 n) ∞ (N k)]

private theorem eventually_pullback_inner_le_near_chart
    (g : RiemannianMetric n M) (h : ∀ k, RiemannianMetric n (N k))
    (e : ∀ k, M → N k) (p : M)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hp : p ∈ c.source)
    (hc : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target)
    (hsmooth : ∀ A : Set M, IsCompact A → ∀ᶠ k in atTop,
      ∀ x ∈ A, ContMDiffAt (𝓡 n) (𝓡 n) ∞ (e k) x)
    {r : ℝ} (hr : 0 < r) (hAt : Metric.closedBall (c p) r ⊆ c.target)
    (hmetric :
      TendstoUniformlyOn (fun k => (h k).pullbackCoefficients (e k ∘ c.symm))
        (g.pullbackCoefficients c.symm) atTop (Metric.closedBall (c p) r)) :
    ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      (h k).inner (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v)
          (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤ 2 * g.inner x v v := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hi (x : E) (hx : x ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible :=
    ⟨(hc ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  let A := Metric.closedBall (c p) r
  have hA : IsCompact A := isCompact_closedBall _ _
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) A := by
    intro x hx
    exact (g.contDiffAt_pullbackCoefficients
      (hc ⟨x, hAt hx⟩).contMDiffAt).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ A, ∀ v : E, v ≠ 0 →
      0 < g.pullbackCoefficients c.symm x v v := by
    intro x hx v hv
    apply g.pos
    intro hz
    apply hv
    apply (hi x (hAt hx)).injective
    rw [map_zero]
    exact hz
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hA hcont hpos
  have hconv := (Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hmetric a ha
  have hAc : IsCompact (c.symm '' A) := hA.image_of_continuousOn
    (c.symm.continuousOn.mono hAt)
  let U := c.source ∩ c ⁻¹' Metric.ball (c p) r
  have hU : U ∈ 𝓝 p := inter_mem (c.open_source.mem_nhds hp)
    ((c.continuousOn.continuousAt (c.open_source.mem_nhds hp)).preimage_mem_nhds
      (Metric.ball_mem_nhds (c p) (by positivity)))
  refine ⟨U, hU, ?_⟩
  filter_upwards [hconv, hsmooth _ hAc] with k hk hks x hx v
  have hxc : c x ∈ A := Metric.ball_subset_closedBall hx.2
  have hxi := hi (c x) (hAt hxc)
  let w : E := (mfderiv (𝓡 n) (𝓡 n) c.symm (c x)).inverse v
  have herr : |(h k).pullbackCoefficients (e k ∘ c.symm) (c x) w w -
      g.pullbackCoefficients c.symm (c x) w w| ≤ a * ‖w‖ ^ 2 := by
    have hd : ‖(h k).pullbackCoefficients (e k ∘ c.symm) (c x) -
        g.pullbackCoefficients c.symm (c x)‖ ≤ a := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hk (c x) hxc).le
    calc
      _ ≤ ‖(h k).pullbackCoefficients (e k ∘ c.symm) (c x) -
          g.pullbackCoefficients c.symm (c x)‖ * ‖w‖ * ‖w‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          ((h k).pullbackCoefficients (e k ∘ c.symm) (c x) -
            g.pullbackCoefficients c.symm (c x)).le_opNorm₂ w w
      _ ≤ a * ‖w‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hd (mul_nonneg (norm_nonneg w) (norm_nonneg w))
  have hbound : (h k).pullbackCoefficients (e k ∘ c.symm) (c x) w w ≤
      2 * g.pullbackCoefficients c.symm (c x) w w := by
    have hh := (abs_le.mp herr).2
    linarith [hlower (c x) hxc w]
  have hchain := mfderiv_comp (c x)
    ((hks _ (mem_image_of_mem c.symm hxc)).mdifferentiableAt (by simp))
    ((hc ⟨c x, hAt hxc⟩).contMDiffAt.mdifferentiableAt (by simp))
  have htransport := congrArg (fun y : M =>
    (h k).inner (e k y) (mfderiv (𝓡 n) (𝓡 n) (e k) y v)
      (mfderiv (𝓡 n) (𝓡 n) (e k) y v) ≤ 2 * g.inner y v v) (c.left_inv hx.1)
  apply htransport.mp
  change (h k).inner (e k (c.symm (c x)))
      (mfderiv (𝓡 n) (𝓡 n) (e k ∘ c.symm) (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) (e k ∘ c.symm) (c x) w) ≤
    2 * g.inner (c.symm (c x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) at hbound
  rw [hchain] at hbound
  change (h k).inner (e k (c.symm (c x)))
      (mfderiv (𝓡 n) (𝓡 n) (e k) (c.symm (c x))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w))
      (mfderiv (𝓡 n) (𝓡 n) (e k) (c.symm (c x))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)) ≤
    2 * g.inner (c.symm (c x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) at hbound
  simpa only [w, hxi.self_apply_inverse] using hbound



theorem eventually_pullback_tangentNorm_le_twice_of_chart_convergence
    (g : RiemannianMetric n M) (h : ∀ k, RiemannianMetric n (N k))
    (e : ∀ k, M → N k) {K : Set M} (hK : IsCompact K)
    (hsmooth : ∀ A : Set M, IsCompact A → ∀ᶠ k in atTop,
      ∀ x ∈ A, ContMDiffAt (𝓡 n) (𝓡 n) ∞ (e k) x)
    (hcharts : ∀ p ∈ K,
      ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
        p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
        ∃ r : ℝ, 0 < r ∧ Metric.closedBall (c p) r ⊆ c.target ∧
          TendstoUniformlyOn (fun k => (h k).pullbackCoefficients (e k ∘ c.symm))
            (g.pullbackCoefficients c.symm) atTop (Metric.closedBall (c p) r)) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 n) x,
      (h k).tangentNorm (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤
        2 * g.tangentNorm x v := by
  classical
  have hlocal (p : M) (hp : p ∈ K) : ∃ U ∈ 𝓝 p,
      ∀ᶠ k in atTop, ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
        (h k).inner (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v)
            (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤ 2 * g.inner x v v := by
    obtain ⟨c, hpc, hc, r, hr, hrc, hm⟩ := hcharts p hp
    exact eventually_pullback_inner_le_near_chart g h e p c hpc hc hsmooth hr hrc hm
  choose U hU hbound using hlocal
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' U hU
  have hall := (Filter.eventually_all_finite s.finite_toSet).mpr
    (fun (p : K) (_ : p ∈ s) => hbound p p.property)
  filter_upwards [hall] with k hk x hx v
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
  have hb := hk p hp x hxp v
  have hv : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst v; simp
    · exact (g.pos x v hv).le
  have hb' : (h k).inner (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v)
      (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤ (2 : ℝ) ^ 2 * g.inner x v v := by
    nlinarith
  have hn := Real.sqrt_le_sqrt hb'
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at hn
  exact hn

end PoincareConjecture.AncientCompactness

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalMetricComparisonCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)



theorem eventually_embedding_contMDiffAt_on_compact
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ContMDiffAt (𝓡 3) (𝓡 3) ∞ (G.embedding k) x := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  exact (G.embedding_smooth k ⟨x, hmono hk (hj hx)⟩).contMDiffAt



theorem eventually_terminal_pullback_tangentNorm_le_twice
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hF : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) {t : ℝ} (ht : t ≤ 0) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : G.limitCarrier.tangent x,
      ((S.term (G.subsequence k)).flow.flow.metric t).tangentNorm (G.embedding k x)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v) ≤
        2 * (F.metric t).tangentNorm x v := by
  apply AncientCompactness.eventually_pullback_tangentNorm_le_twice_of_chart_convergence
    (F.metric t) (fun k => (S.term (G.subsequence k)).flow.flow.metric t)
    G.embedding hK
    (fun A hA => S.eventually_embedding_contMDiffAt_on_compact G hA)
  intro q _
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := chartAt E q
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limitCarrier.carrier E ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hcoe : (extChartAt (𝓡 3) q : G.limitCarrier.carrier → E) = c := by
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, c]
  have hsymm : ((extChartAt (𝓡 3) q).symm : E → G.limitCarrier.carrier) = c.symm := by
    simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id, c]
  have htarget : (extChartAt (𝓡 3) q).target = c.target := by
    simp only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ, c]
  obtain ⟨r, hr, hrc⟩ := G.exists_pos_referenceChartBall_radius q
  refine ⟨c, mem_chart_source E q, ?_, 2 * r, by positivity, ?_, ?_⟩
  · intro x
    exact d.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ x.property
  · simpa only [hcoe, htarget] using hrc
  have hzero := S.tendstoUniformlyOn_terminal_bilinearJet_on_closedBall G F hF P
    hcontrol hcomplete q (by positivity : 0 < 2 * r) hrc 0
    (K := {t} ×ˢ Metric.closedBall (extChartAt (𝓡 3) q q) (2 * r))
    (isCompact_singleton.prod (isCompact_closedBall _ _))
    (prod_mono (singleton_subset_iff.mpr (show t ∈ Iic 0 from ht)) subset_rfl)
  have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → ℝ × E)).comp_tendstoUniformlyOn hzero
  change TendstoUniformlyOn
    (fun k (z : ℝ × E) => ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2)
    (fun z : ℝ × E => (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2)
    atTop ({t} ×ˢ Metric.closedBall (extChartAt (𝓡 3) q q) (2 * r)) at hvalue
  have hslice := (hvalue.comp (fun x : E => (t, x))).mono
    (show Metric.closedBall (extChartAt (𝓡 3) q q) (2 * r) ⊆
      (fun x : E => (t, x)) ⁻¹' ({t} ×ˢ Metric.closedBall (extChartAt (𝓡 3) q q) (2 * r))
      from fun x hx => ⟨mem_singleton t, hx⟩)
  simpa only [Function.comp_def, hcoe, hsymm] using hslice

end PoincareConjecture.NormalizedKappaSolutionSequence
