import PoincareConjecture.Proofs.M30.Thm11_1.CanonicalRelatedNeck
import PoincareConjecture.Proofs.M30.Thm11_1.SelectedStaticStageSlices
import PoincareConjecture.Proofs.M28.Mathlib.FiniteBufferedChartCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 100000 in




theorem exists_static_limit_related_neck_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (_hC : RicciFlowCurvatureTheory.{u})
        {S : GeneralizedBlowupSequence.{u}}
        {epsilon canonicalConstant kappa r0 mu : ℝ}
        (_H : M30CommonBlowupControls S epsilon canonicalConstant kappa r0 mu),
        epsilon ≤ epsilon0 → GeneralizedBlowupBoundedDistance S →
      ∀ (G : PartialPointedMetricConvergence
          (terminalComponentMetric S) (terminalComponentBase S) 1),
        G.limitCarrier.metricComplete G.limitMetric →
      ∀ (D : LeviCivitaData G.limitMetric) (x : G.limitCarrier.carrier),
        4 < D.scalarCurvature x →
        (∃ N : EpsilonNeck G.limitMetric,
          N.epsilon = 2 * epsilon ∧ N.connection = D ∧
            D.scalarCurvature x ≤
              max 1 (2 * canonicalConstant) * D.scalarCurvature N.center) ∨
          IsCompact (univ : Set G.limitCarrier.carrier) := by
  classical
  obtain ⟨epsilon0, hpositive, hsmall, hrelated⟩ :=
    exists_canonical_slice_related_neck_threshold.{u, 0, 0}
  refine ⟨epsilon0, hpositive, hsmall, ?_⟩
  intro hC S epsilon canonicalConstant kappa r0 mu H hepsilon hbound G hcomplete D x hx
  let : ConnectedSpace G.limitCarrier.carrier :=
    connectedSpace_iff_univ.mpr G.limitCarrier.connected
  let : MetricSpace G.limitCarrier.carrier := G.limitCarrier.metricSpaceOf G.limitMetric
  have hepsilonpos := H.epsilon_pos
  let rho := max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (canonicalConstant / 2) + 1
  have hrho : 0 < rho := by
    have hp : 0 < (2 * Real.pi + 2 * epsilon⁻¹) / 2 := by positivity
    have hm := le_max_left ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (canonicalConstant / 2)
    dsimp only [rho]
    linarith
  let R := 2 * rho + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  have hbuffer : 2 * rho < R := by dsimp only [R]; linarith
  have hclosure : IsCompact (closure (G.limitMetric.ball x R)) := by
    apply IsCompact.of_isClosed_subset
      (G.limitMetric.isCompact_closedBall_of_metricComplete hcomplete x R) isClosed_closure
    apply closure_minimal
      (fun y (hy : G.limitMetric.edist x y < ENNReal.ofReal R) => hy.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  let K := closure (G.limitMetric.ball x R) ∪ {G.base}
  have hK : IsCompact K := hclosure.union isCompact_singleton
  have hpK : G.base ∈ K := Or.inr (mem_singleton G.base)
  have hxK : x ∈ K := by
    apply Or.inl
    apply subset_closure
    change EDist.edist x x < ENNReal.ofReal R
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hR
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  let Y : TopologicalSpace.Opens G.limitCarrier.carrier :=
    ⟨G.exhaustion j, G.exhaustion_open j⟩
  obtain ⟨centers, radius, hcenters, hcover⟩ :=
    hK.exists_finite_buffered_extChart_ball_cover (𝓡 3) (G.exhaustion_open j) hj
  let ι := {q : G.limitCarrier.carrier // q ∈ centers}
  let q : ι → G.limitCarrier.carrier := Subtype.val
  let c (i : ι) := extChartAt (𝓡 3) (q i)
  let U (i : ι) := ball (c i (q i)) (2 * radius (q i))
  let L (i : ι) := closedBall (c i (q i)) (radius (q i))
  have hr (i : ι) : 0 < radius (q i) := (hcenters i.val i.property).2.1
  have hU (i : ι) : IsOpen (U i) := isOpen_ball
  have hL (i : ι) : IsCompact (L i) := isCompact_closedBall _ _
  have hLU (i : ι) : L i ⊆ U i :=
    closedBall_subset_ball (by linarith [hr i])
  have hUtarget (i : ι) : U i ⊆ (c i).target :=
    fun _ hz => ((hcenters i.val i.property).2.2 (ball_subset_closedBall hz)).1
  have hUimage (i : ι) : ∀ z ∈ U i, (c i).symm z ∈ G.exhaustion j :=
    fun _ hz => ((hcenters i.val i.property).2.2 (ball_subset_closedBall hz)).2
  let psi (i : ι) (z : EuclideanSpace ℝ (Fin 3)) : Y :=
    if hz : z ∈ U i then ⟨(c i).symm z, hUimage i z hz⟩
    else ⟨G.base, G.base_in_exhaustion j⟩
  have hpsival (i : ι) (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ U i) :
      (psi i z).val = (c i).symm z := by simp only [psi, dif_pos hz]
  have hpsi (i : ι) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (psi i) (U i) := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff Y (psi i) (U i) z).mp
    exact (((contMDiffOn_extChartAt_symm (q i)).mono (hUtarget i)) z hz).congr
      (fun y hy => hpsival i y hy) (hpsival i z hz)
  have hLtarget (i : ι) : L i ⊆ (c i).target := (hLU i).trans (hUtarget i)
  have hLimage (i : ι) : (c i).symm '' L i ⊆ G.exhaustion j := by
    rintro _ ⟨z, hz, rfl⟩
    exact hUimage i z (hLU i hz)
  have hcover' : K ⊆ ⋃ i : ι, (c i).symm '' L i := by
    intro y hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hcover hy)
    obtain ⟨hzmem, hzy⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨⟨z, hzmem⟩, ?_⟩
    exact ⟨extChartAt (𝓡 3) z y, ball_subset_closedBall hzy.2,
      (extChartAt (𝓡 3) z).left_inv hzy.1⟩
  obtain ⟨W, T, B, _hW, hT, _hB, N, E, P, himage, hP, hterminal, _hcurv⟩ :=
    exists_source_flows_on_static_stage hC H hbound G hcomplete j
  let d := ⌊(2 * epsilon)⁻¹⌋₊ + 1
  obtain ⟨s, hs, _hdelta, hgood, _hjets0, _hscalar0, hjets, hscalar, hmaps⟩ :=
    exists_good_static_stage_slice_sequence S G j N hT E P himage hP hterminal
      D epsilon canonicalConstant (fun k => H.canonical (G.subsequence (k + N)))
      q U L hU hUtarget hL hLU psi hpsi hpsival K hK hj hcover' d x hrho hbuffer
      (show closure (G.limitMetric.ball x R) ⊆ K from subset_union_left)
  let nu (k : ℕ) := G.subsequence (k + N)
  let Q (k : ℕ) := S.scale (nu k)
  let t (k : ℕ) := (S.base (nu k)).1 + s k / Q k
  let f (k : ℕ) (y : G.limitCarrier.carrier) :=
    (E k).embedding.forward (s k) (hs k) (G.embedding (k + N) y).val
  let h : ∀ k, RiemannianMetric 3 ((S.flow (nu k)).slice (t k)).carrier :=
    fun k => M13.scaleSmoothMetric ((S.flow (nu k)).metric (t k)) (Q k)
      (S.base_scalar_pos (nu k))
  change TendstoUniformlyOn
    (fun k y => (S.flow (nu k)).scalar ⟨t k, f k y⟩ / Q k)
    D.scalarCurvature atTop K at hscalar
  have hhigh : ∀ᶠ k in atTop, 4 < (S.flow (nu k)).scalar ⟨t k, f k x⟩ / Q k :=
    (hscalar.tendsto_at hxK).eventually (Ioi_mem_nhds hx)
  have hcanonical : ∀ᶠ k in atTop, Nonempty
      (GeneralizedCanonicalControl (F := S.flow (nu k))
        (t k) (f k x) epsilon canonicalConstant) := by
    filter_upwards [hhigh] with k hk
    exact (hgood k).2 (f k x) ((lt_div_iff₀ (S.base_scalar_pos (nu k))).mp hk).le
  have hballK : G.limitMetric.ball x (2 * rho) ⊆ K := by
    intro y hy
    apply Or.inl
    apply subset_closure
    exact hy.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le)
  have hcapture : ∀ᶠ k in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3)
      G.limitCarrier.carrier ((S.flow (nu k)).slice (t k)).carrier ∞,
      e.source = G.exhaustion j ∧
      (e : G.limitCarrier.carrier → ((S.flow (nu k)).slice (t k)).carrier) = f k ∧
      (h k).ball (f k x) rho ⊆ f k '' K := by
    filter_upwards [hmaps] with k hk
    obtain ⟨e, hes, hef, _het, hball⟩ := hk
    exact ⟨e, hes, hef, hball.trans (image_mono hballK)⟩
  exact hrelated (ι := ι) G.limitMetric D G.base x
    (terminal_static_limit_base_scalar S G D) hx epsilon canonicalConstant
    hepsilonpos hepsilon (fun k => S.flow (nu k)) t Q
    (fun k => S.base_scalar_pos (nu k)) f (G.exhaustion j) K
    (G.exhaustion_open j) (G.exhaustion_connected j).isPreconnected
    hK hj hpK hxK q L hL hLtarget hLimage hcover' hscalar hcanonical hcapture hjets

end PoincareConjecture.M30
