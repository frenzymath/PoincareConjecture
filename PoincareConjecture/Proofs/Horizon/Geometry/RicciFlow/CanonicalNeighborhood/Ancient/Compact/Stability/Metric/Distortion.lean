import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

private theorem eventually_local_abs_inner_sub_le
    (hconv : M23TerminalMetricConvergence G e) (p : G.limit.carrier.carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ V ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
      |normalizedKappaPullbackInnerValue (e k) 0 x v v -
          (G.limit.flow.flow.metric 0).inner x v v| ≤
        epsilon * (G.limit.flow.flow.metric 0).inner x v v := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) p
  let g := G.limit.flow.flow.metric 0
  have hpc : p ∈ c.source := mem_extChartAt_source p
  obtain ⟨K, hKnhds, hKt, hK⟩ := local_compact_nhds
    ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (c.map_source hpc))
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) K := by
    intro z hz
    exact (g.contDiffAt_pullbackCoefficients
      ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (hKt hz)))).continuousAt.continuousWithinAt
  have hpos : ∀ z ∈ K, ∀ w : E, w ≠ 0 → 0 < g.pullbackCoefficients c.symm z w w := by
    intro z hz w hw
    apply g.pos
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := 𝓡 3) (hKt hz)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
    intro hzero
    have h := congrArg (fun L ↦ L w) hcomp
    change mfderiv (𝓡 3) (𝓡 3) c (c.symm z)
      (mfderiv (𝓡 3) (𝓡 3) c.symm z w) = w at h
    erw [hzero, map_zero] at h
    exact hw h.symm
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hcont hpos
  have hcoeff := Metric.tendstoUniformlyOn_iff.mp
    (hconv.terminalPullbackCoefficients_tendstoUniformlyOn p hK hKt)
    (epsilon * a) (mul_pos hepsilon ha)
  let V := c.source ∩ c ⁻¹' K
  have hV : V ∈ 𝓝 p := inter_mem
    ((isOpen_extChartAt_source (I := 𝓡 3) p).mem_nhds hpc)
    ((continuousAt_extChartAt (I := 𝓡 3) p).preimage_mem_nhds hKnhds)
  refine ⟨V, hV, ?_⟩
  filter_upwards [hcoeff] with k hk x hx v
  let w := mfderiv (𝓡 3) (𝓡 3) c x v
  have hnorm : ‖(e k).terminalPullbackCoefficients p (c x) -
      g.pullbackCoefficients c.symm (c x)‖ ≤ epsilon * a := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hk (c x) hx.2).le
  have hbound : |(e k).terminalPullbackCoefficients p (c x) w w -
      g.pullbackCoefficients c.symm (c x) w w| ≤
        epsilon * g.pullbackCoefficients c.symm (c x) w w := by
    calc
      _ ≤ ‖(e k).terminalPullbackCoefficients p (c x) -
          g.pullbackCoefficients c.symm (c x)‖ * ‖w‖ * ‖w‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          ((e k).terminalPullbackCoefficients p (c x) -
            g.pullbackCoefficients c.symm (c x)).le_opNorm₂ w w
      _ ≤ epsilon * (a * ‖w‖ ^ 2) := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg w) (norm_nonneg w))
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower (c x) hx.2 w) hepsilon.le
  have hderiv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 3) hx.1
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hderiv
  have hv : mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w = v :=
    congrArg (fun L ↦ L v) hderiv
  have hcx : c.symm (c x) = x := c.left_inv hx.1
  change |normalizedKappaPullbackInnerValue (e k) 0 (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w) -
    g.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)| ≤
    epsilon * g.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w) at hbound
  erw [hv, hcx] at hbound
  exact hbound

theorem eventually_abs_inner_sub_le_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      |normalizedKappaPullbackInnerValue (e k) 0 x v v -
          (G.limit.flow.flow.metric 0).inner x v v| ≤
        epsilon * (G.limit.flow.flow.metric 0).inner x v v := by
  classical
  choose V hV hbound using fun p ↦ hconv.eventually_local_abs_inner_sub_le p hepsilon
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover V (fun x _ ↦ hV x)
  filter_upwards [s.eventually_all.mpr (fun x _ ↦ hbound x)] with k hk x hx v
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
  exact hk p hp x hxp v

theorem eventually_tangentNorm_bounds_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      Real.sqrt (normalizedKappaPullbackInnerValue (e k) 0 x v v) ≤
        C * (G.limit.flow.flow.metric 0).tangentNorm x v ∧
      (G.limit.flow.flow.metric 0).tangentNorm x v ≤
        C * Real.sqrt (normalizedKappaPullbackInnerValue (e k) 0 x v v) := by
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hupper : 0 < C ^ 2 - 1 := by nlinarith
  have hlower : 0 < 1 - C⁻¹ ^ 2 := by
    have hi := inv_pos.mpr hCpos
    have hi1 := (inv_lt_one₀ hCpos).mpr hC
    nlinarith
  let epsilon := min (C ^ 2 - 1) (1 - C⁻¹ ^ 2)
  filter_upwards [hconv.eventually_abs_inner_sub_le_on_compact hK
    (lt_min hupper hlower)] with k hk x hx v
  let a := (G.limit.flow.flow.metric 0).inner x v v
  let b := normalizedKappaPullbackInnerValue (e k) 0 x v v
  have ha : 0 ≤ a := by
    by_cases hv : v = 0
    · simp [a, hv]
    · exact ((G.limit.flow.flow.metric 0).pos x v hv).le
  have hh := abs_le.mp (hk x hx v)
  change -(epsilon * a) ≤ b - a ∧ b - a ≤ epsilon * a at hh
  have he1 : epsilon ≤ C ^ 2 - 1 := min_le_left _ _
  have he2 : epsilon ≤ 1 - C⁻¹ ^ 2 := min_le_right _ _
  have hab : b ≤ C ^ 2 * a := by
    have hm := mul_le_mul_of_nonneg_right he1 ha
    nlinarith [hh.2]
  have hba : a ≤ C ^ 2 * b := by
    have hh' : C⁻¹ ^ 2 * a ≤ b := by
      have hm := mul_le_mul_of_nonneg_right he2 ha
      nlinarith [hh.1]
    have hm := mul_le_mul_of_nonneg_left hh' (sq_nonneg C)
    have hi : C ^ 2 * C⁻¹ ^ 2 = 1 := by field_simp
    simpa only [← mul_assoc, hi, one_mul] using hm
  change Real.sqrt b ≤ C * Real.sqrt a ∧ Real.sqrt a ≤ C * Real.sqrt b
  constructor
  · rw [← Real.sqrt_sq hCpos.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hab
  · rw [← Real.sqrt_sq hCpos.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hba

end M23TerminalMetricConvergence

end PoincareConjecture
