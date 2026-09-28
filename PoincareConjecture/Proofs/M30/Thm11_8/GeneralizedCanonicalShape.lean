import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalSliceShape
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedScalarConvergence
import PoincareConjecture.Proofs.M30.Generalized.Restriction
import PoincareConjecture.Proofs.M28.Mathlib.FiniteBufferedChartCover
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.SpatialContinuity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric
import PoincareConjecture.Proofs.M04.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.measurableSpace FlowCarrier.borelSpace FlowCarrier.secondCountable

private theorem shape_uniform_at_moving_time
    {Y : Type v} [TopologicalSpace Y] {Z : Type w} [UniformSpace Z]
    {I : Set ℝ} {K : Set Y} (hK : IsCompact K)
    {A : ℕ → ℝ × Y → Z} {B : ℝ × Y → Z}
    (hA : TendstoUniformlyOn A B atTop (I ×ˢ K))
    (hB : ContinuousOn B (I ×ˢ K)) {t : ℝ} (ht : t ∈ I)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[I] t)) :
    TendstoUniformlyOn (fun k y => A k (s k, y)) (fun y => B (t, y)) atTop K := by
  intro U hU
  obtain ⟨V, hV, hsymm, hcomp⟩ := comp_symm_of_uniformity hU
  obtain ⟨O, hO, hclose⟩ := hK.mem_uniformity_of_prod
    (f := fun a y => B (a, y)) hB ht hV
  filter_upwards [hA V hV, hs.eventually hO,
    hs.eventually self_mem_nhdsWithin] with k hk hks hki
  intro y hy
  exact hcomp (SetRel.prodMk_mem_comp (hsymm (hclose (s k) hks y hy))
    (hk (s k, y) ⟨hki, hy⟩))

set_option maxHeartbeats 1200000 in

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_generalized_canonical_slice_shape_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
        (G : GeneralizedBlowupConvergence S J)
        (epsilon C : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
        (∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
          (S.flow (G.subsequence k)) epsilon C
          (S.base (G.subsequence k)).1 (S.base (G.subsequence k)).2) →
      ∀ (t : ℝ), t ∈ J →
        (∃ delta : ℝ, 0 < delta ∧ Icc (t - delta) t ⊆ J) →
      ∀ x : G.limit.carrier.carrier,
        let g := G.limit.flow.metric t
        let D := G.limit.flow.connection t
        4 < D.scalarCurvature x →
        (∃ N : EpsilonNeck g,
          N.epsilon = 2 * epsilon ∧ N.connection = D ∧ N.center = x) ∨
        (∃ N : EpsilonNeck g, ∃ W : Set G.limit.carrier.carrier,
          N.epsilon = 2 * epsilon ∧ N.connection = D ∧
          IsOpen W ∧ IsCompact (closure W) ∧ x ∈ W ∧ x ∉ N.carrier ∧
          frontier W = N.central_sphere ∧
          W ∩ N.carrier = N.region (-N.epsilon⁻¹) 0 ∧
          closure W ⊆ g.ball x
            (8 * max 1 C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) ∧
          (4 * max 1 C * D.scalarCurvature x)⁻¹ ≤ N.scale ^ 2 ∧
          N.scale ^ 2 ≤ 4 * max 1 C / D.scalarCurvature x) ∨
        IsCompact (univ : Set G.limit.carrier.carrier) := by
  classical
  obtain ⟨epsilon0, hpositive, hsmall, hshape⟩ :=
    exists_canonical_slice_shape_threshold.{u, u, u}
  refine ⟨epsilon0, hpositive, hsmall, ?_⟩
  intro S J G epsilon C hepsilon hepsilon0 hdense t ht hleft x
  dsimp only
  intro hx
  let g := G.limit.flow.metric t
  let D := G.limit.flow.connection t
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  let rho := max (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8 + 1
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [le_max_right (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8]
  let R := 2 * rho + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  have hbuffer : 2 * rho < R := by dsimp only [R]; linarith
  let K := closure (g.ball x R)
  have hK : IsCompact K := by
    apply IsCompact.of_isClosed_subset
      (g.isCompact_closedBall_of_metricComplete (G.limit.complete t ht) x R) isClosed_closure
    apply closure_minimal
      (fun y (hy : g.edist x y < ENNReal.ofReal R) => hy.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hxK : x ∈ K := by
    apply subset_closure
    change EDist.edist x x < ENNReal.ofReal R
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hR
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G hK
  let Y : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
  obtain ⟨centers, radius, hcenters, hcover⟩ :=
    hK.exists_finite_buffered_extChart_ball_cover (𝓡 3) (G.exhaustion.space_open j) hj
  let ι := {q : G.limit.carrier.carrier // q ∈ centers}
  let q : ι → G.limit.carrier.carrier := Subtype.val
  let c (i : ι) := extChartAt (𝓡 3) (q i)
  let V (i : ι) := ball (c i (q i)) (2 * radius (q i))
  let L (i : ι) := closedBall (c i (q i)) (radius (q i))
  have hr (i : ι) : 0 < radius (q i) := (hcenters i.val i.property).2.1
  have hV (i : ι) : IsOpen (V i) := isOpen_ball
  have hL (i : ι) : IsCompact (L i) := isCompact_closedBall _ _
  have hLV (i : ι) : L i ⊆ V i := closedBall_subset_ball (by linarith [hr i])
  have hVtarget (i : ι) : V i ⊆ (c i).target :=
    fun _ hz => ((hcenters i.val i.property).2.2 (ball_subset_closedBall hz)).1
  have hVimage (i : ι) : ∀ z ∈ V i, (c i).symm z ∈ G.exhaustion.space j :=
    fun _ hz => ((hcenters i.val i.property).2.2 (ball_subset_closedBall hz)).2
  have hLtarget (i : ι) : L i ⊆ (c i).target := (hLV i).trans (hVtarget i)
  have hLimage (i : ι) : (c i).symm '' L i ⊆ G.exhaustion.space j := by
    rintro _ ⟨z, hz, rfl⟩
    exact hVimage i z (hLV i hz)
  have hcover' : K ⊆ ⋃ i : ι, (c i).symm '' L i := by
    intro y hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hcover hy)
    obtain ⟨hzmem, hzy⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨⟨z, hzmem⟩, extChartAt (𝓡 3) z y,
      ball_subset_closedBall hzy.2, (extChartAt (𝓡 3) z).left_inv hzy.1⟩
  obtain ⟨delta, hdelta, hIJ⟩ := hleft
  let I : Set ℝ := Icc (t - delta) t
  have htI : t ∈ I := ⟨by linarith, le_rfl⟩
  have hIdiff : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  let W : SpacetimeInterval := {
    domain := I
    ordConnected := ordConnected_Icc
    nontrivial := ⟨t - delta, ⟨le_rfl, by linarith⟩,
      t, htI, (show t - delta < t by linarith).ne⟩ }
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((G.exhaustion.time_cofinal I isCompact_Icc hIJ).and (eventually_ge_atTop j))
  have htime (k : ℕ) : I ⊆ Icc (-G.exhaustion.time (k + N)) 0 :=
    (hN (k + N) (Nat.le_add_left N k)).1
  have hstage (k : ℕ) : j ≤ k + N := (hN (k + N) (Nat.le_add_left N k)).2
  let nu (k : ℕ) := G.subsequence (k + N)
  let Q (k : ℕ) := S.scale (nu k)
  have hQ (k : ℕ) : 0 < Q k := S.base_scalar_pos (nu k)
  let a (k : ℕ) := (S.base (nu k)).1
  let E (k : ℕ) : GeneralizedFlowCylinder (S.flow (nu k)) G.limit.sliceCarrier
      (a k) (Q k) W.domain Y :=
    Cylinder.restrict (G.embedding (k + N)) (htime k)
      (G.exhaustion.space_increasing (hstage k))
  have htPhysical (k : ℕ) : a k + t / Q k ∈ (S.flow (nu k)).interval := by
    apply ((S.flow (nu k)).slice_nonempty_iff _).mp
    exact ⟨(E k).forward t htI G.limit.base⟩
  have htzero : t ≤ 0 := (htime 0 htI).2
  have hchoice (k : ℕ) : ∃ s : ℝ, s ∈ I ∧
      t - 1 / ((k : ℝ) + 1) < s ∧ s ≤ t ∧
      generalizedSliceStrongCanonicalNeighborhoods (S.flow (nu k)) epsilon C
        (4 * Q k) (a k + s / Q k) := by
    let b := min delta (1 / ((k : ℝ) + 1))
    have hb : 0 < b := by dsimp only [b]; positivity
    have hbdelta : b ≤ delta := min_le_left _ _
    have hbsmall : b ≤ 1 / ((k : ℝ) + 1) := min_le_right _ _
    obtain ⟨u, _hu, hlower, hupper, hgood⟩ :=
      hdense (k + N) (a k + t / Q k) (htPhysical k)
        (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg htzero (hQ k).le))
        (a k + (t - b) / Q k)
        (by linarith only [div_lt_div_of_pos_right (sub_lt_self t hb) (hQ k)])
    let s := Q k * (u - a k)
    have hslower : t - b < s := by
      have hh := (div_lt_iff₀ (hQ k)).mp (show (t - b) / Q k < u - a k by linarith)
      dsimp only [s]
      nlinarith
    have hsupper : s ≤ t := by
      have hh := (le_div_iff₀ (hQ k)).mp (show u - a k ≤ t / Q k by linarith)
      dsimp only [s]
      nlinarith
    have hclock : a k + s / Q k = u := by
      dsimp only [s]
      field_simp [(hQ k).ne']
      ring
    refine ⟨s, ⟨by linarith, hsupper⟩, by linarith, hsupper, ?_⟩
    rw [hclock]
    exact hgood
  choose s hs hslower hsupper hgood using hchoice
  have hsLimit : Tendsto s atTop (𝓝[I] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Metric.tendsto_nhds.mpr ?_, Eventually.of_forall hs⟩
    intro eta heta
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds heta)]
      with k hk
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hsupper k))]
    linarith [hslower k]
  let time (k : ℕ) := a k + s k / Q k
  let h (k : ℕ) : RiemannianMetric 3 ((S.flow (nu k)).slice (time k)).carrier :=
    M13.scaleSmoothMetric ((S.flow (nu k)).metric (time k)) (Q k) (hQ k)
  let e (k : ℕ) : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.carrier.carrier
      ((S.flow (nu k)).slice (time k)).carrier ∞ := {
    toPartialEquiv := (Cylinder.spatialHomeomorph (E k) ⟨s k, hs k⟩).toPartialEquiv
    open_source := Y.isOpen
    open_target := Cylinder.isOpen_spatial_image (E k) ⟨s k, hs k⟩
    contMDiffOn_toFun := (E k).forward_smooth (s k) (hs k)
    contMDiffOn_invFun := (E k).inverse_smooth (s k) (hs k) }
  let f (k : ℕ) : G.limit.carrier.carrier → ((S.flow (nu k)).slice (time k)).carrier := e k
  have hsource (k : ℕ) : (e k).source = G.exhaustion.space j := rfl
  have hjets (i : ι) (m : ℕ) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((h k).pullbackCoefficients (f k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop (L i) := by
    have hfull := (tendstoUniformlyOn_generalized_bilinear_spatial_jets G (q i) m
      (isCompact_Icc.prod (hL i)) (Set.prod_mono hIJ (hLtarget i))).seq_tendstoUniformlyOn
        (fun k => k + N) (tendsto_add_atTop_nat N)
    have hcoeff := G.limit.flow.smooth.contDiffOn_spacetime_pullbackCoefficients_within
      (hV i) ((contMDiffOn_extChartAt_symm (q i)).mono (hVtarget i))
    have hcontinuous := M28.continuousOn_spatialJet_of_within hIdiff (hV i)
      (hcoeff.mono (Set.prod_mono hIJ (Subset.rfl))) m
    have hh := shape_uniform_at_moving_time (hL i) hfull
      (hcontinuous.mono (Set.prod_mono_right (hLV i))) htI hsLimit
    convert hh using 1
    funext k z
    have heq : (fun y => generalizedPullbackCoefficients G (k + N) (q i) (s k, y)) =
        (h k).pullbackCoefficients (f k ∘ (c i).symm) := by
      funext y
      simp only [generalizedPullbackCoefficients, dif_pos (htime k (hs k))]
      rfl
    rw [heq]
  have hscalar : TendstoUniformlyOn
      (fun k y => (S.flow (nu k)).scalar ⟨time k, f k y⟩ / Q k)
      D.scalarCurvature atTop K := by
    let A (k : ℕ) (p : ℝ × G.limit.carrier.carrier) : ℝ :=
      if hp : p.1 ∈ Icc (-G.exhaustion.time (k + N)) 0 then
        (S.flow (nu k)).scalar ((G.embedding (k + N)).pointMap p.1 hp p.2) / Q k
      else 0
    let B (p : ℝ × G.limit.carrier.carrier) :=
      (G.limit.flow.connection p.1).scalarCurvature p.2
    have hfull : TendstoUniformlyOn A B atTop (I ×ˢ K) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro eta heta
      filter_upwards [(tendsto_add_atTop_nat N).eventually
        (eventually_generalized_scalar_error G isCompact_Icc hIJ hK heta)] with k hk
      intro p hp
      have hh := hk.2.2 p.1 hp.1 (htime k hp.1) p.2 hp.2
      simpa only [A, B, dif_pos (htime k hp.1), Real.dist_eq, abs_sub_comm] using hh
    have hcont : ContinuousOn B (I ×ˢ K) :=
      G.limit.flow.contMDiffOn_scalarCurvature.continuousOn.mono
        (Set.prod_mono hIJ (subset_univ K))
    have hh := shape_uniform_at_moving_time hK hfull hcont htI hsLimit
    convert hh using 1
    funext k y
    simp only [A, dif_pos (htime k (hs k))]
    rfl
  have hhigh : ∀ᶠ k in atTop, 4 < (S.flow (nu k)).scalar ⟨time k, f k x⟩ / Q k :=
    (hscalar.tendsto_at hxK).eventually (Ioi_mem_nhds hx)
  have hcanonical : ∀ᶠ k in atTop, Nonempty
      (GeneralizedCanonicalControl (F := S.flow (nu k)) (time k) (f k x) epsilon C) := by
    filter_upwards [hhigh] with k hk
    exact hgood k (f k x) ((lt_div_iff₀ (hQ k)).mp hk).le
  have hinverse := eventually_inverse_tangent_bound_of_finite_chart_jets g h e K
    (fun k => (hsource k).symm ▸ hj) q L hL hLtarget hcover' (fun i => hjets i 0)
  have hmaps : ∀ᶠ k in atTop, ∃ e' : PartialDiffeomorph (𝓡 3) (𝓡 3)
      G.limit.carrier.carrier ((S.flow (nu k)).slice (time k)).carrier ∞,
      e'.source = G.exhaustion.space j ∧
      (e' : G.limit.carrier.carrier → ((S.flow (nu k)).slice (time k)).carrier) = f k ∧
      (h k).ball (f k x) rho ⊆ f k '' K := by
    filter_upwards [hinverse] with k hk
    refine ⟨e k, hsource k, rfl, ?_⟩
    have hh := g.ball_subset_image_ball_of_inverse_tangentNorm_le (h k)
      (e k).toOpenPartialHomeomorph x hR (by norm_num : (0 : ℝ) < 2) hbuffer hK
      ((hsource k).symm ▸ hj)
      (fun z hz => ((e k).contMDiffOn_invFun.contMDiffAt
        ((e k).open_target.mem_nhds hz)).of_le (by simp)) hk
    apply hh.trans
    apply image_mono
    intro z hz
    exact subset_closure (hz.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le))
  exact hshape (ι := ι) g D x hx epsilon C hepsilon hepsilon0
    (fun k => S.flow (nu k)) time Q hQ f (G.exhaustion.space j) K
    (G.exhaustion.space_open j) hK hj hxK q L hL hLtarget hLimage hcover'
    hscalar hcanonical hmaps (fun i m _ => hjets i m)

end PoincareConjecture.M30
