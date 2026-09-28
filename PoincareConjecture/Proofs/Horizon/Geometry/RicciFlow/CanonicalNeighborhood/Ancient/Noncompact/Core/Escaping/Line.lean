import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Segments
import Mathlib.Order.Filter.Ultrafilter.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

theorem M23TerminalExtension.exists_minimizing_line_of_source_arcs
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    (arc : ∀ k, ℝ → (S.term (G.subsequence k)).carrier.carrier)
    (hbounded : ∀ t : ℝ, ∃ A : ℝ, 0 < A ∧ ∀ᶠ k in atTop,
      arc k t ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base A)
    (hdist : ∀ s t : ℝ, Tendsto (fun k =>
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist (arc k s) (arc k t)).toReal)
      atTop (𝓝 |s - t|)) :
    ∃ γ : ℝ → G.limit.carrier.carrier, ∀ s t : ℝ,
      (G.limit.flow.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  classical
  obtain ⟨e, he, _, hconv⟩ := hterminal.terminal_embedding
  let g := G.limit.flow.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  let a := fun k t => ((e k).inverse (0, arc k t)).2
  have hbase := fun k => (he k).2
  choose A hA hbound using hbounded
  have hcompact (t : ℝ) : IsCompact (closure (g.ball G.limit.base (2 * A t))) :=
    g.isCompact_closure_ball_of_metricComplete (G.limit.flow.complete 0 le_rfl)
      G.limit.base (2 * A t)
  have hpre (t : ℝ) : ∀ᶠ k in atTop, a k t ∈ closure (g.ball G.limit.base (2 * A t)) := by
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hcompact t)
    have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
    filter_upwards [hbound t, eventually_ge_atTop j,
      hconv.eventually_source_ball_subset_terminal_image hbase (hA t)
        (by norm_num : (1 : ℝ) < 2)] with k hk hkj hcover
    obtain ⟨z, hz, hzeq⟩ := hcover hk
    have hzstage := hmono hkj (hj (subset_closure hz))
    let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
    have hinv : a k t = z := by
      change E.symm (arc k t) = z
      change E z = arc k t at hzeq
      rw [← hzeq, E.left_inv hzstage]
    rw [hinv]
    exact subset_closure hz
  have hlimit : ∀ t : ℝ, ∃ q : G.limit.carrier.carrier,
      Tendsto (fun k => a k t) (hyperfilter ℕ : Filter ℕ) (𝓝 q) := by
    intro t
    obtain ⟨q, _, hq⟩ := (hcompact t).ultrafilter_le_nhds'
      ((hyperfilter ℕ).map fun k => a k t)
      ((hpre t).filter_mono Nat.hyperfilter_le_atTop)
    rw [Ultrafilter.coe_map] at hq
    exact ⟨q, hq⟩
  choose γ hγ using hlimit
  have hinverse (s t : ℝ) : Tendsto (fun k => dist (a k s) (a k t)) atTop (𝓝 |s - t|) := by
    apply hconv.tendsto_terminal_inverse_distance hbase (fun k => arc k s)
      (fun k => arc k t) (A := max (A s) (A t)) (lt_max_of_lt_left (hA s))
    · exact (hbound s).mono fun k hk =>
        hk.trans_le (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact (hbound t).mono fun k hk =>
        hk.trans_le (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    · exact hdist s t
  refine ⟨γ, fun s t => ?_⟩
  have hd : dist (γ s) (γ t) = |s - t| :=
    tendsto_nhds_unique ((hγ s).dist (hγ t))
      ((hinverse s t).mono_left Nat.hyperfilter_le_atTop)
  rw [← ENNReal.ofReal_toReal (g.edist_ne_top (γ s) (γ t))]
  exact congrArg ENNReal.ofReal hd

theorem M23TerminalExtension.exists_minimizing_line_of_nearby_necks
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    (hnoncompact : ∀ k, NoncompactSpace (S.term (G.subsequence k)).carrier.carrier)
    (soul : ∀ k, RiemannianMetric.PointSoulData
      ((S.term (G.subsequence k)).flow.flow.metric 0))
    (neck : ∀ k, EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0))
    (hsmall : ∀ k, (neck k).epsilon ≤ neckSeparationThreshold)
    {Bcenter : ℝ} (hBcenter : 0 ≤ Bcenter)
    (hnear : ∀ k, (((S.term (G.subsequence k)).flow.flow.metric 0).edist
      (neck k).center (S.term (G.subsequence k)).base).toReal ≤ Bcenter)
    {B : ℝ} (hB : 0 ≤ B) (hscale : ∀ k, (neck k).scale ≤ B)
    (hescape : Tendsto (fun k =>
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist
        (soul k).center (S.term (G.subsequence k)).base).toReal) atTop atTop) :
    ∃ γ : ℝ → G.limit.carrier.carrier, ∀ s t : ℝ,
      (G.limit.flow.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  classical
  let C := (2 * Real.pi) * B + Bcenter
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (by positivity) hB) hBcenter
  let d := fun k => (((S.term (G.subsequence k)).flow.flow.metric 0).edist
    (soul k).center (S.term (G.subsequence k)).base).toReal
  let radius := fun k => (d k - (C + 1)) / 2
  have hradius : Tendsto radius atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [hescape.eventually_ge_atTop (2 * a + C + 1)] with k hk
    dsimp [radius, d]
    change 2 * a + C + 1 ≤ d k at hk
    change a ≤ (d k - (C + 1)) / 2
    linarith
  have hwindow (k : ℕ) : ∃ arc : ℝ → (S.term (G.subsequence k)).carrier.carrier,
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist
        (arc 0) (S.term (G.subsequence k)).base).toReal ≤ C ∧
      ∀ s t : ℝ, |s| ≤ radius k → |t| ≤ radius k →
        ((S.term (G.subsequence k)).flow.flow.metric 0).edist (arc s) (arc t) =
          ENNReal.ofReal |s - t| := by
    let := hnoncompact k
    let g := (S.term (G.subsequence k)).flow.flow.metric 0
    by_cases hr : 0 < radius k
    · have hdiam : (2 * Real.pi) * (neck k).scale ≤ (2 * Real.pi) * B :=
        mul_le_mul_of_nonneg_left (hscale k) (by positivity)
      have hfar : radius k + (2 * Real.pi) * (neck k).scale <
          (g.edist (soul k).center (neck k).center).toReal := by
        have htriangle := g.toReal_edist_triangle (soul k).center (neck k).center
          (S.term (G.subsequence k)).base
        have hn := hnear k
        change d k ≤ _ at htriangle
        dsimp [radius, C] at hr ⊢
        linarith
      obtain ⟨arc, _, hbase, hdist⟩ := (soul k).exists_minimizing_window_through_neck
        ((S.term (G.subsequence k)).flow.complete 0 le_rfl) (neck k) (hsmall k) hr.le hfar
      refine ⟨arc, ?_, hdist⟩
      exact (g.toReal_edist_triangle (arc 0) (neck k).center
        (S.term (G.subsequence k)).base).trans (add_le_add (hbase.trans hdiam) (hnear k))
    · refine ⟨fun _ => (S.term (G.subsequence k)).base, ?_, ?_⟩
      · simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self,
          ENNReal.toReal_zero] using hC
      · intro s t hs ht
        have hs0 : s = 0 := abs_eq_zero.mp
          (le_antisymm (hs.trans (le_of_not_gt hr)) (abs_nonneg s))
        have ht0 : t = 0 := abs_eq_zero.mp
          (le_antisymm (ht.trans (le_of_not_gt hr)) (abs_nonneg t))
        simp only [hs0, ht0, sub_self, abs_zero, ENNReal.ofReal_zero,
          RiemannianMetric.edist, Manifold.riemannianEDist_self]
  choose arc hbase hdist using hwindow
  apply hterminal.exists_minimizing_line_of_source_arcs arc
  · intro t
    refine ⟨C + |t| + 1, by positivity, ?_⟩
    filter_upwards [hradius.eventually_ge_atTop |t|,
      hradius.eventually_ge_atTop 0] with k ht h0
    let g := (S.term (G.subsequence k)).flow.flow.metric 0
    let : MetricSpace (S.term (G.subsequence k)).carrier.carrier :=
      (S.term (G.subsequence k)).carrier.metricSpaceOf g
    have hsegment : dist (arc k 0) (arc k t) = |t| := by
      change (g.edist (arc k 0) (arc k t)).toReal = |t|
      rw [hdist k 0 t (by simpa only [abs_zero] using h0) ht]
      simp only [zero_sub, abs_neg, ENNReal.toReal_ofReal (abs_nonneg t)]
    have htriangle := dist_triangle (S.term (G.subsequence k)).base (arc k 0) (arc k t)
    rw [dist_comm (S.term (G.subsequence k)).base (arc k 0), hsegment] at htriangle
    apply (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top _ _)).mpr
    change dist (S.term (G.subsequence k)).base (arc k t) < C + |t| + 1
    have hb : dist (arc k 0) (S.term (G.subsequence k)).base ≤ C := hbase k
    linarith
  · intro s t
    apply tendsto_const_nhds.congr'
    filter_upwards [hradius.eventually_ge_atTop |s|,
      hradius.eventually_ge_atTop |t|] with k hs ht
    rw [hdist k s t hs ht, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem M23TerminalExtension.exists_minimizing_line_of_escaping_souls
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hnoncompact : ∀ k, NoncompactSpace (S.term (G.subsequence k)).carrier.carrier)
    (soul : ∀ k, RiemannianMetric.PointSoulData
      ((S.term (G.subsequence k)).flow.flow.metric 0))
    (neck : ∀ k, EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0))
    (hsmall : ∀ k, (neck k).epsilon ≤ neckSeparationThreshold)
    (hcenter : ∀ k, (neck k).center = (S.term (G.subsequence k)).base)
    {B : ℝ} (hB : 0 ≤ B) (hscale : ∀ k, (neck k).scale ≤ B)
    (hescape : Tendsto (fun k =>
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist
        (soul k).center (S.term (G.subsequence k)).base).toReal) atTop atTop) :
    ∃ γ : ℝ → G.limit.carrier.carrier, ∀ s t : ℝ,
      (G.limit.flow.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  apply T.exists_minimizing_line_of_nearby_necks hnoncompact soul neck hsmall
    (Bcenter := 0) le_rfl (fun k => ?_) hB hscale hescape
  rw [hcenter k]
  simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero,
    le_refl]

end PoincareConjecture
