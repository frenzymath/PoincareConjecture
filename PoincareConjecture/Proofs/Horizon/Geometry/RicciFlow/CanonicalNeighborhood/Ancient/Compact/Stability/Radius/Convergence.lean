import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.ScaleConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.Distortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem eventually_scalarCoreRadius_le_add_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (hlimit : ∀ x, 0 < (G.limit.flow.flow.connection 0).scalarCurvature x)
    (hsource : ∀ k x,
      0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature x)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ p ∈ K,
      scalarCoreRadius ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((S.term (G.subsequence k)).flow.flow.connection 0)
          ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (hsource k)
          ((e k).toFun (0, p)).2 ≤
        scalarCoreRadius (G.limit.flow.flow.metric 0) (G.limit.flow.flow.connection 0)
          (G.limit.flow.complete 0 le_rfl) hlimit p + δ := by
  let g := G.limit.flow.flow.metric 0
  let D := G.limit.flow.flow.connection 0
  let r := scalarCoreRadius g D (G.limit.flow.complete 0 le_rfl) hlimit
  have hr (p : G.limit.carrier.carrier) : 0 < r p :=
    (scalarCoreRadius_spec g D (G.limit.flow.complete 0 le_rfl) hlimit p).1
  have hrcont : Continuous r :=
    continuous_scalarCoreRadius g D (G.limit.flow.complete 0 le_rfl) hlimit
  obtain ⟨b, hb⟩ := (hK.image hrcont).bddAbove
  let B := max b 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hrB : ∀ p ∈ K, r p ≤ B := fun p hp ↦
    (hb (mem_image_of_mem r hp)).trans (le_max_left _ _)
  let C := 1 + δ / (4 * (B + 1))
  have hC : 1 < C := by
    dsimp [C]
    linarith [div_pos hδ (by positivity : 0 < 4 * (B + 1))]
  have hCpos : 0 < C := zero_lt_one.trans hC
  let η := δ / (4 * C)
  have hη : 0 < η := by dsimp [η]; positivity
  have hCη : C * η = δ / 4 := by dsimp [η]; field_simp
  have hCr : ∀ p ∈ K, C * r p ≤ r p + δ / 4 := by
    intro p hp
    have hmul := mul_le_mul_of_nonneg_left
      (show r p ≤ B + 1 by linarith [hrB p hp])
      (div_nonneg hδ.le (by positivity : 0 ≤ 4 * (B + 1)))
    have hcancel : δ / (4 * (B + 1)) * (B + 1) = δ / 4 := by
      field_simp
    dsimp [C]
    rw [hcancel] at hmul
    nlinarith
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  let : ProperSpace G.limit.carrier.carrier :=
    g.properSpace_toMetricSpace (G.limit.flow.complete 0 le_rfl)
  obtain ⟨R, _, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 G.limit.base
  let L := Metric.closedBall G.limit.base (R + B + η)
  have hL : IsCompact L := isCompact_closedBall _ _
  have hballL (p : G.limit.carrier.carrier) (hp : p ∈ K) :
      g.ball p (r p + η) ⊆ L := by
    intro x hx
    have hpR : dist G.limit.base p ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm] using hKR hp
    have hpx : dist p x < r p + η := by
      simpa only [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm] using hx
    change dist x G.limit.base ≤ R + B + η
    rw [dist_comm]
    linarith [dist_triangle G.limit.base p x, hrB p hp]
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hL
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  have hscale := Metric.tendstoUniformlyOn_iff.mp
    (hconv.tendstoUniformlyOn_terminal_scalarScale hfixed hlimit hL) δ hδ
  filter_upwards [eventually_ge_atTop j, hscale,
    hconv.eventually_tangentNorm_bounds_on_compact hL hC] with k hk hscale hmetric p hp
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  let gk := (S.term (G.subsequence k)).flow.flow.metric 0
  let Dk := (S.term (G.subsequence k)).flow.flow.connection 0
  obtain ⟨x, hpx, hxscale⟩ := exists_scalarCoreRadius_witness g D
    (G.limit.flow.complete 0 le_rfl) hlimit p
  have hxball : x ∈ g.ball p (r p + η) := by
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm,
      RiemannianMetric.toMetricSpace_dist]
    change (g.edist p x).toReal ≤ r p at hpx
    linarith
  have hsourceball : g.ball p (r p + η) ⊆ E.source :=
    (hballL p hp).trans (hj.trans (hmono hk))
  have hmap := g.image_ball_subset_ball_of_tangentNorm_le gk E p hCpos hsourceball
    (fun z hz ↦ ((e k).spatial_contMDiffAt (G.exhaustion_open k)
      (mem_Iic.mpr le_rfl) hz).of_le (by simp))
    (fun z hz v ↦ (hmetric z (hballL p hp hz) v).1)
  have himage : E x ∈ gk.ball (E p) (C * (r p + η)) :=
    hmap (mem_image_of_mem E hxball)
  have hdistance : (gk.edist (E p) (E x)).toReal < r p + δ := by
    have hdist : (gk.edist (E p) (E x)).toReal < C * (r p + η) :=
      (ENNReal.toReal_lt_toReal (gk.edist_ne_top _ _) ENNReal.ofReal_ne_top).mpr himage |>.trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hCpos.le (add_nonneg (hr p).le hη.le)))
    nlinarith [hCr p hp, hCη]
  have hscalarScale : (Real.sqrt (Dk.scalarCurvature (E x)))⁻¹ < r p + δ := by
    have hs := hscale x (hballL p hp hxball)
    change dist (Real.sqrt (D.scalarCurvature x))⁻¹
      (Real.sqrt (Dk.scalarCurvature (E x)))⁻¹ < δ at hs
    rw [hxscale, Real.dist_eq] at hs
    change |r p - (Real.sqrt (Dk.scalarCurvature (E x)))⁻¹| < δ at hs
    linarith [(abs_lt.mp hs).1]
  exact (scalarCoreRadius_le_max_distance_scale gk Dk
    ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (hsource k) (E p) (E x)).trans
      (max_le hdistance.le hscalarScale.le)



theorem eventually_scalarCoreRadius_le_mul_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (hlimit : ∀ x, 0 < (G.limit.flow.flow.connection 0).scalarCurvature x)
    (hsource : ∀ k x,
      0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature x)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ p ∈ K,
      scalarCoreRadius ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((S.term (G.subsequence k)).flow.flow.connection 0)
          ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (hsource k)
          ((e k).toFun (0, p)).2 ≤
        C * scalarCoreRadius (G.limit.flow.flow.metric 0) (G.limit.flow.flow.connection 0)
          (G.limit.flow.complete 0 le_rfl) hlimit p := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall (by simp)
  let r := scalarCoreRadius (G.limit.flow.flow.metric 0) (G.limit.flow.flow.connection 0)
    (G.limit.flow.complete 0 le_rfl) hlimit
  have hcont : Continuous r := continuous_scalarCoreRadius _ _ _ _
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hrp : 0 < r p := (scalarCoreRadius_spec _ _ _ _ p).1
  have hδ : 0 < (C - 1) * r p := mul_pos (sub_pos.mpr hC) hrp
  filter_upwards [hconv.eventually_scalarCoreRadius_le_add_on_compact
    hfixed hlimit hsource hK hδ] with k hk q hq
  apply (hk q hq).trans
  have hm := mul_le_mul_of_nonneg_left (hmin hq) (sub_nonneg.mpr hC.le)
  change r q + (C - 1) * r p ≤ C * r q
  linarith

end M23TerminalMetricConvergence

end PoincareConjecture
