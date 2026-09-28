import PoincareConjecture.Statements.M30Providers
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCanonicalShape
import PoincareConjecture.Proofs.M30.Thm11_8.LocalCompactNeckSide
import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalShortChord
import PoincareConjecture.Proofs.M30.Thm11_8.OpposingShortChord
import PoincareConjecture.Proofs.M30.Thm11_8.OpposingVertices
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

private theorem exists_chart_ball_avoiding_two_points
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (y p z : M) (hyp : y ≠ p) (hyz : y ≠ z) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ p ∉ U ∧ z ∉ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) ∧
      ∃ r : ℝ, 0 < r ∧ g.ball y r ⊆ U := by
  let : T1Space M := T2Space.t1Space
  let E := EuclideanSpace ℝ (Fin 3)
  let c := chartAt E y
  have hyc : y ∈ c.source := mem_chart_source E y
  have hopen : IsOpen (({p, z} : Set M)ᶜ) :=
    ((Set.finite_singleton z).insert p).isClosed.isOpen_compl
  have hyavoid : y ∈ ({p, z} : Set M)ᶜ := by simp [hyp, hyz]
  have hO := c.symm.isOpen_inter_preimage hopen
  have hyO : c y ∈ c.target ∩ c.symm ⁻¹' ({p, z} : Set M)ᶜ := by
    exact ⟨c.map_source hyc, by simpa only [mem_preimage, c.left_inv hyc] using hyavoid⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO (c y) hyO
  have htarget : Metric.ball (c y) r ⊆ c.symm.source :=
    fun x hx => (hball hx).1
  let U := c.symm '' Metric.ball (c y) r
  have hU : IsOpen U := c.symm.isOpen_image_of_subset_source Metric.isOpen_ball htarget
  have hyU : y ∈ U := ⟨c y, Metric.mem_ball_self hr, c.left_inv hyc⟩
  have havoid : U ⊆ ({p, z} : Set M)ᶜ := by
    rintro x ⟨w, hw, rfl⟩
    exact (hball hw).2
  have hpU : p ∉ U := fun hp => havoid hp (by simp)
  have hzU : z ∉ U := fun hz => havoid hz (by simp)
  let B : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall (c y) r
  have hBsource : B.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hBtarget : B.target = Metric.ball (c y) r :=
    OpenPartialHomeomorph.univBall_target _ hr
  have hBimage : B '' (univ : Set E) = Metric.ball (c y) r := by
    simpa only [hBsource, hBtarget] using B.image_source_eq_target
  let eB : E ≃ₜ Metric.ball (c y) r := (Homeomorph.Set.univ E).symm.trans
    (B.homeomorphOfImageSubsetSource (by rw [hBsource]) hBimage)
  let eU : Metric.ball (c y) r ≃ₜ U :=
    c.symm.homeomorphOfImageSubsetSource htarget rfl
  let : MetricSpace M := g.toMetricSpace
  obtain ⟨r0, hr0, hsmall⟩ := Metric.isOpen_iff.mp hU y hyU
  refine ⟨U, hU, hyU, hpU, hzU, ⟨(eB.trans eU).symm⟩, r0, hr0, ?_⟩
  rwa [g.toMetricSpace_ball] at hsmall

private theorem mul_inverse_sqrt_lt_of_square_lt
    {R a d : ℝ} (hR : 0 < R) (_ha : 0 < a) (hd : 0 < d)
    (hlarge : (a / d) ^ 2 < R) : a * R ^ (-1 / 2 : ℝ) < d := by
  have hroot : a / d < Real.sqrt R := by
    nlinarith [Real.sq_sqrt hR.le, Real.sqrt_nonneg R, div_pos _ha hd]
  have hmul : a < d * Real.sqrt R := by
    simpa only [mul_comm] using (div_lt_iff₀ hd).mp hroot
  have hpower : R ^ (-1 / 2 : ℝ) = (Real.sqrt R)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow]
  rw [hpower, ← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.sqrt_pos.mpr hR)).mpr hmul

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.measurableSpace FlowCarrier.borelSpace FlowCarrier.secondCountable

theorem exists_noncompact_limit_scalar_anchor_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ),
        0 < epsilon → epsilon ≤ epsilon0 → 0 < C →
        GeneralizedBoundedDistanceHypotheses S epsilon C →
      ∀ (T : ℝ), 0 < T →
      ∀ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
        ¬ IsCompact (univ : Set G.limit.carrier.carrier) →
        ∃ y : G.limit.carrier.carrier, ∃ B : ℝ,
          0 ≤ B ∧ ∀ t, t ∈ Ioc (-T) 0 →
            (G.limit.flow.connection t).scalarCurvature y ≤ B := by
  classical
  obtain ⟨epsilonShape, hShapePos, hShapeMax, hshape⟩ :=
    exists_generalized_canonical_slice_shape_threshold.{u}
  let etaStar := min (1 / 4 : ℝ)
    (min (1 / (4 * neckDepthConstant * (2 * Real.pi + 2)))
      (1 / (16 * Real.pi * neckDepthConstant)))
  have hStarPos : 0 < etaStar := by
    dsimp only [etaStar]
    exact lt_min (by norm_num) (lt_min (by positivity [neckDepthConstant_pos])
      (by positivity [neckDepthConstant_pos]))
  refine ⟨min epsilonShape (etaStar / 2),
    lt_min hShapePos (by positivity), (min_le_left _ _).trans hShapeMax, ?_⟩
  intro S epsilon C hepsilon hepsilonLe _hC H T _hT G hnoncompact
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : NoncompactSpace G.limit.carrier.carrier := ⟨hnoncompact⟩
  let eta := 2 * epsilon
  have heta : 0 < eta := mul_pos (by norm_num) hepsilon
  have hetaStar : eta ≤ etaStar := by
    have h := hepsilonLe.trans (min_le_right _ _)
    dsimp only [eta]
    linarith
  have hetaQuarter : eta ≤ 1 / 4 := hetaStar.trans (min_le_left _ _)
  have hetaSmall : eta ≤ 1 / (4 * neckDepthConstant * (2 * Real.pi + 2)) :=
    hetaStar.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaChord : 8 * Real.pi * neckDepthConstant * eta ≤ 1 / 2 := by
    have h := hetaStar.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hd : 0 < 16 * Real.pi * neckDepthConstant := by
      positivity [neckDepthConstant_pos]
    have hm := (le_div_iff₀ hd).mp h
    nlinarith
  let g0 := G.limit.flow.metric 0
  obtain ⟨L, hL, hdistances⟩ := exists_finite_limit_distance_error P.m04 P.m06 G.limit
  obtain ⟨d, hdLarge, y, z, hpy, hyz, hpz⟩ :=
    exists_opposing_vertices_of_metricComplete g0
      (G.limit.complete 0 G.limit.zero_mem) G.limit.base L
  have hd : 0 < d := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hdLarge)
  have hLsmall : L ≤ d / 2 := by
    have h := (le_max_right _ _).trans_lt hdLarge
    linarith
  have hyp : y ≠ G.limit.base := by
    intro h
    rw [h] at hpy
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self,
      ENNReal.toReal_zero] at hpy
    linarith
  have hyzNe : y ≠ z := by
    intro h
    rw [h] at hyz
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self,
      ENNReal.toReal_zero] at hyz
    linarith
  have hypDistance : (g0.edist y G.limit.base).toReal = d := by
    let : MetricSpace G.limit.carrier.carrier := g0.toMetricSpace
    change dist y G.limit.base = d
    rw [dist_comm]
    exact hpy
  obtain ⟨U, hU, _hyU, hpU, hzU, ⟨hchart⟩, r0, hr0, hballU⟩ :=
    exists_chart_ball_avoiding_two_points g0 y G.limit.base z hyp hyzNe
  let B := max 4 (max (((2 * Real.pi + 2 / eta) / d) ^ 2)
    (max ((2 * Real.pi / r0) ^ 2) ((8 * max 1 C / d) ^ 2)))
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
  refine ⟨y, B, hB, ?_⟩
  intro t ht
  by_contra hbound
  have hBR : B < (G.limit.flow.connection t).scalarCurvature y := lt_of_not_ge hbound
  let g := G.limit.flow.metric t
  let D := G.limit.flow.connection t
  let R := D.scalarCurvature y
  have hRfour : 4 < R := (le_max_left _ _).trans_lt hBR
  have hR : 0 < R := lt_trans (by norm_num) hRfour
  have hlargeNeck : ((2 * Real.pi + 2 / eta) / d) ^ 2 < R :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hBR
  have hlargeSphere : (2 * Real.pi / r0) ^ 2 < R :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hBR
  have hlargeCap : (8 * max 1 C / d) ^ 2 < R :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hBR
  have hneckRadius : (2 * Real.pi + 2 / eta) * R ^ (-1 / 2 : ℝ) < d :=
    mul_inverse_sqrt_lt_of_square_lt hR (by positivity) hd hlargeNeck
  have hsphereRadius : (2 * Real.pi) * R ^ (-1 / 2 : ℝ) < r0 :=
    mul_inverse_sqrt_lt_of_square_lt hR (by positivity) hr0 hlargeSphere
  have hcapRadius : (8 * max 1 C) * R ^ (-1 / 2 : ℝ) < d :=
    mul_inverse_sqrt_lt_of_square_lt hR (by positivity) hd hlargeCap
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  have hdist (v w : G.limit.carrier.carrier) : dist v w = (g.edist v w).toReal := rfl
  let a := dist y G.limit.base
  let b := dist y z
  have haPair : d ≤ a ∧ a ≤ d + L := by
    change d ≤ (g.edist y G.limit.base).toReal ∧
      (g.edist y G.limit.base).toReal ≤ d + L
    have h := hdistances t ht y G.limit.base
    change (g0.edist y G.limit.base).toReal ≤ _ ∧ _ ≤
      (g0.edist y G.limit.base).toReal + L at h
    simpa only [hypDistance] using h
  have hbPair : d ≤ b ∧ b ≤ d + L := by
    change d ≤ (g.edist y z).toReal ∧ (g.edist y z).toReal ≤ d + L
    have h := hdistances t ht y z
    change (g0.edist y z).toReal ≤ _ ∧ _ ≤ (g0.edist y z).toReal + L at h
    simpa only [hyz] using h
  have hend : 2 * d ≤ dist G.limit.base z := by
    change 2 * d ≤ (g.edist G.limit.base z).toReal
    have h := (hdistances t ht G.limit.base z).1
    change (g0.edist G.limit.base z).toReal ≤ _ at h
    simpa only [hpz] using h
  have ha : 0 < a := hd.trans_le haPair.1
  have hb : 0 < b := hd.trans_le hbPair.1
  obtain ⟨gamma, hgamma0, hgamma1, hgamma, _⟩ :=
    g.exists_smooth_metric_segment_of_complete (G.limit.complete t ht) hdist y G.limit.base
  obtain ⟨sigma, hsigma0, hsigma1, hsigma, _⟩ :=
    g.exists_smooth_metric_segment_of_complete (G.limit.complete t ht) hdist y z
  change gamma a = G.limit.base at hgamma1
  change sigma b = z at hsigma1
  have hsec : D.NonnegativeSectionalCurvature := fun x v w =>
    D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x
      (G.limit.nonnegative_curvature_operator t ht x) v w
  have hcontradiction (ell : ℝ) (hell : 0 < ell) (hellA : ell ≤ a) (hellB : ell ≤ b)
      (hchord : dist (gamma ell) (sigma ell) ≤
        (8 * Real.pi * neckDepthConstant * eta) * ell) : False := by
    refine not_short_chord_of_opposing_vertices g D hdist (G.limit.complete t ht) hsec
      hd hL.le hLsmall haPair.1 haPair.2 hbPair.1 hbPair.2 hgamma hsigma
      (hgamma0.trans hsigma0.symm) ?_ hell hellA hellB ?_
    · simpa only [hgamma1, hsigma1] using hend
    · apply hchord.trans
      have h := mul_le_mul_of_nonneg_right hetaChord hell.le
      nlinarith
  have hleft : ∃ delta : ℝ, 0 < delta ∧ Icc (t - delta) t ⊆ Ioc (-T) 0 := by
    refine ⟨(t + T) / 2, by linarith [ht.1], ?_⟩
    intro s hs
    exact ⟨by linarith [ht.1, hs.1], hs.2.trans ht.2⟩
  rcases hshape G epsilon C hepsilon (hepsilonLe.trans (min_le_left _ _))
      (fun k => H.canonical (G.subsequence k)) t ht hleft y hRfour with
    ⟨N, hNepsilon, hNconnection, hNcenter⟩ | hcap | hcompact
  · have hscale : N.scale = R ^ (-1 / 2 : ℝ) := by
      simpa only [hNconnection, hNcenter] using N.scale_eq_scalar
    have hwholeRadius : (2 * Real.pi + 2 * N.epsilon⁻¹) * N.scale < d := by
      simpa only [hNepsilon, hscale, div_eq_mul_inv] using hneckRadius
    have hwhole (x : G.limit.carrier.carrier) (hx : x ∈ N.carrier) : dist y x < d := by
      have h := N.edist_center_le_of_mem_carrier hx
      rw [hNcenter] at h
      rw [hdist]
      exact (ENNReal.toReal_le_of_le_ofReal
        (by positivity [N.scale_pos, N.epsilon_pos]) h).trans_lt
        hwholeRadius
    have hpNeck : G.limit.base ∉ N.carrier := fun hp =>
      (not_lt_of_ge haPair.1) (hwhole G.limit.base hp)
    have hzNeck : z ∉ N.carrier := fun hz => (not_lt_of_ge hbPair.1) (hwhole z hz)
    have hslab : N.coordinate_map ''
        (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) ⊆ N.carrier := by
      intro x hx
      have hi : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
      exact ((N.mem_coordinate_slab_iff (by linarith) (by linarith)).mp hx).1
    have hcentral : N.central_sphere ⊆ U := by
      intro x hx
      apply hballU
      have h := N.edist_central_sphere_le_two_pi_mul_scale N.center_on_central_sphere hx
      rw [hNcenter] at h
      have hupper := ENNReal.toReal_le_of_le_ofReal
        (show 0 ≤ (2 * Real.pi) * N.scale by positivity [N.scale_pos]) h
      have hsmall : (g0.edist y x).toReal < r0 := by
        apply ((hdistances t ht y x).1.trans hupper).trans_lt
        simpa only [hscale] using hsphereRadius
      change g0.edist y x < ENNReal.ofReal r0
      exact (ENNReal.lt_ofReal_iff_toReal_lt (g0.edist_ne_top y x)).mpr hsmall
    obtain ⟨A, hA, _hAc, hAU, hfront, hhalf⟩ :=
      exists_precompact_neck_side_of_central_sphere_subset_chart N hU hchart hcentral
    have hpA : G.limit.base ∉ A := fun hp => hpU (hAU (subset_closure hp))
    have hzA : z ∉ A := fun hz => hzU (hAU (subset_closure hz))
    obtain ⟨ell, hell, hellA, hellB, _hdepth, _habsolute, hchord⟩ :=
      exists_equal_radius_short_chord_of_neck_side g N hdist
        (hNepsilon.symm ▸ hetaQuarter) (hNepsilon.symm ▸ hetaSmall) hA hfront hhalf
        ha hb hgamma hsigma (hgamma0.trans hNcenter.symm) (hsigma0.trans hNcenter.symm)
        (by simpa only [hgamma1] using hpA) (by simpa only [hsigma1] using hzA)
        (by simpa only [hgamma1] using fun hx => hpNeck (hslab hx))
        (by simpa only [hsigma1] using fun hx => hzNeck (hslab hx))
    apply hcontradiction ell hell hellA hellB
    simpa only [hNepsilon] using hchord
  · obtain ⟨N, W, hNepsilon, _hNconnection, hW, _hWcompact, hyW, hyNeck,
      hfront, _hoverlap, hradius, _hscaleLower, _hscaleUpper⟩ := hcap
    have hpW : G.limit.base ∉ W := by
      intro hp
      have h := ENNReal.toReal_lt_of_lt_ofReal (hradius (subset_closure hp))
      exact (not_lt_of_ge haPair.1) (h.trans hcapRadius)
    have hzW : z ∉ W := by
      intro hz
      have h := ENNReal.toReal_lt_of_lt_ofReal (hradius (subset_closure hz))
      exact (not_lt_of_ge hbPair.1) (h.trans hcapRadius)
    obtain ⟨ell, hell, hellA, hellB, _hdepth, _habsolute, hchord⟩ :=
      exists_equal_radius_short_chord_of_cap_side g N hdist
        (hNepsilon.symm ▸ hetaQuarter) hW hfront hyW hyNeck ha hb hgamma hsigma
        hgamma0 hsigma0 (by simpa only [hgamma1] using hpW)
        (by simpa only [hsigma1] using hzW)
    apply hcontradiction ell hell hellA hellB
    simpa only [hNepsilon] using hchord
  · exact hnoncompact hcompact

end PoincareConjecture.M30
