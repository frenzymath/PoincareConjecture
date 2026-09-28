import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.M07.Geometry.Manifold.VectorField.Derivation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
  (G : PartialPointedMetricConvergence g p A)


theorem exhaustion_monotone : Monotone G.exhaustion := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  exact monotone_nat_of_le_succ (fun j => subset_closure.trans (G.exhaustion_step j))



theorem exists_exhaustion_superset {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K) :
    ∃ j, K ⊆ G.exhaustion j := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  exact hK.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) G.exhaustion_monotone.directed_le

private theorem eventually_inner_le_near_chart (q : G.limitCarrier.carrier) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∃ N ∈ 𝓝 q, ∀ᶠ k in atTop, ∀ x ∈ N, x ∈ G.exhaustion k →
      ∀ v : TangentSpace (𝓡 n) x,
        (g (G.subsequence k)).inner (G.embedding k x)
          (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v)
          (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v) ≤
        2 * G.limitMetric.inner x v v := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 n) q
  have hq : q ∈ c.source := mem_extChartAt_source q
  have hi (z : E) (hz : z ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible :=
    Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hz
  have hc (z : E) (hz : z ∈ c.target) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hz)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (c.map_source hq))
  let C := Metric.closedBall (c q) (r / 2)
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCt : C ⊆ c.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  have hcont : ContinuousOn (G.limitMetric.pullbackCoefficients c.symm) C := by
    intro z hz
    exact (G.limitMetric.contDiffAt_pullbackCoefficients
      (hc z (hCt hz))).continuousAt.continuousWithinAt
  have hpos : ∀ z ∈ C, ∀ v : E, v ≠ 0 →
      0 < G.limitMetric.pullbackCoefficients c.symm z v v := by
    intro z hz v hv
    apply G.limitMetric.pos
    intro hzero
    apply hv
    apply (hi z (hCt hz)).injective
    rw [map_zero]
    exact hzero
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hC hcont hpos
  have hmetric : TendstoUniformlyOn
      (fun k => (g (G.subsequence k)).pullbackCoefficients (G.embedding k ∘ c.symm))
      (G.limitMetric.pullbackCoefficients c.symm) atTop C := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using!
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → E)).comp_tendstoUniformlyOn (G.metric_jets q 0 C hC hCt)
  have hconv := (Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hmetric a ha
  let N := c.source ∩ c ⁻¹' Metric.ball (c q) (r / 2)
  have hN : N ∈ 𝓝 q := inter_mem ((isOpen_extChartAt_source q).mem_nhds hq)
    (((continuousOn_extChartAt q).continuousAt
      ((isOpen_extChartAt_source q).mem_nhds hq)).preimage_mem_nhds
        (Metric.ball_mem_nhds (c q) (by positivity)))
  refine ⟨N, hN, ?_⟩
  filter_upwards [hconv] with k hk x hx hxstage v
  have hxc : c x ∈ C := Metric.ball_subset_closedBall hx.2
  have hxi := hi (c x) (hCt hxc)
  let w : E := (mfderiv (𝓡 n) (𝓡 n) c.symm (c x)).inverse v
  let B := G.limitMetric.pullbackCoefficients c.symm (c x)
  let Bk := (g (G.subsequence k)).pullbackCoefficients (G.embedding k ∘ c.symm) (c x)
  have herr : |Bk w w - B w w| ≤ a * ‖w‖ ^ 2 := by
    have hd : ‖Bk - B‖ ≤ a := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hk (c x) hxc).le
    calc
      _ ≤ ‖Bk - B‖ * ‖w‖ * ‖w‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using (Bk - B).le_opNorm₂ w w
      _ ≤ a * ‖w‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hd (mul_nonneg (norm_nonneg w) (norm_nonneg w))
  have hbound : Bk w w ≤ 2 * B w w := by
    have hh := (abs_le.mp herr).2
    have hb := hlower (c x) hxc w
    change a * ‖w‖ ^ 2 ≤ B w w at hb
    linarith
  have hmap : MDifferentiableAt (𝓡 n) (𝓡 n) (G.embedding k) (c.symm (c x)) := by
    rw [c.left_inv hx.1]
    exact (G.embedding_smooth k ⟨x, hxstage⟩).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (c x) hmap ((hc (c x) (hCt hxc)).mdifferentiableAt (by simp))
  change (g (G.subsequence k)).inner (G.embedding k (c.symm (c x)))
      (mfderiv (𝓡 n) (𝓡 n) (G.embedding k ∘ c.symm) (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) (G.embedding k ∘ c.symm) (c x) w) ≤
    2 * G.limitMetric.inner (c.symm (c x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) at hbound
  have hchainw : mfderiv (𝓡 n) (𝓡 n) (G.embedding k ∘ c.symm) (c x) w =
      mfderiv (𝓡 n) (𝓡 n) (G.embedding k) (c.symm (c x)) v := by
    rw [hchain]
    change mfderiv (𝓡 n) (𝓡 n) (G.embedding k) (c.symm (c x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x)
        ((mfderiv (𝓡 n) (𝓡 n) c.symm (c x)).inverse v)) = _
    rw [hxi.self_apply_inverse]
  rw [hchainw] at hbound
  have htransport := congrArg (fun z : G.limitCarrier.carrier =>
    (g (G.subsequence k)).inner (G.embedding k z)
      (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) z v)
      (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) z v) ≤
      2 * G.limitMetric.inner z v v) (c.left_inv hx.1)
  apply htransport.mp
  simpa only [w, hxi.self_apply_inverse] using hbound




theorem eventually_pullback_inner_le_twice {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 n) x,
      (g (G.subsequence k)).inner (G.embedding k x)
        (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v)
        (mfderiv (𝓡 n) (𝓡 n) (G.embedding k) x v) ≤
      2 * G.limitMetric.inner x v v := by
  classical
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  choose N hN hbound using fun q => G.eventually_inner_le_near_chart q
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' (fun q (_ : q ∈ K) => N q)
    (fun q (_ : q ∈ K) => hN q)
  have hall := (Filter.eventually_all_finite s.finite_toSet).mpr
    (fun (q : K) (_ : q ∈ s) => hbound q)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  filter_upwards [hall, eventually_ge_atTop j] with k hk hjk x hx v
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hs hx)
  exact hk q hq x hxq (G.exhaustion_monotone hjk (hj hx)) v

end PoincareConjecture.M30.PartialPointedMetricConvergence
