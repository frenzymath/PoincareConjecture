import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.CenterOpenness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainStatic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.TransportedScalarFamily














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

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




theorem exists_open_eventually_transported_strongNeck_centers
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    {δ ε : ℝ} (N : StrongEvolvingNeck G.limit.flow 0 δ)
    (hδε : δ < ε) (hεsmall : ε < 1 / 200) :
    ∃ U : Set G.limit.carrier.carrier, IsOpen U ∧ N.center ∈ U ∧
      ∀ᶠ k in atTop, ∀ x ∈ U,
        ∃ Q : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 ε,
          Q.center = ((e k).toFun (0, x)).2 := by
  have hδ : 0 < δ := N.terminal_epsilon ▸ N.terminal_neck.epsilon_pos
  have hε : 0 < ε := hδ.trans hδε
  have hhalf : ε < 1 / 2 := hεsmall.trans (by norm_num : (1 / 200 : ℝ) < 1 / 2)
  have hsmall : N.terminal_neck.epsilon < 1 / 200 := by
    rw [N.terminal_epsilon]
    exact hδε.trans hεsmall
  have hcompact := N.terminal_neck.isCompact_closure_carrier
    (G.limit.flow.complete 0 le_rfl)
  have hR : 0 < (G.limit.flow.flow.connection 0).scalarCurvature N.center := by
    simpa only [N.terminal_connection, N.terminal_center] using N.terminal_neck.scalar_center_pos
  have hclose : RoundCylinderFamilyClose N.terminal_neck.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => (G.limit.flow.flow.connection 0).scalarCurvature N.center *
        roundCylinderPullback
          (G.limit.flow.flow.metric (u / (G.limit.flow.flow.connection 0).scalarCurvature N.center))
          N.terminal_neck.coordinate_map z v w) := by
    rw [N.terminal_epsilon]
    simpa only [zero_add] using N.metric_comparison
  have hscalar := hconv.tendsto_terminal_scalarCurvature_prod
    (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx) N.center
  have hfamily := hconv.eventually_terminalNeck_full_scalarNormalized_familyClose hfixed
    N.terminal_neck hcompact hsmall hR hclose
    (Prod.fst : ℕ × G.limit.carrier.carrier → ℕ) tendsto_fst hscalar
  have hstatic := hconv.eventually_terminalStaticNeck_full_domain hfixed
    N.terminal_neck hcompact hsmall
  let b := δ⁻¹ - ε⁻¹
  have hb : 0 < b := sub_pos.mpr ((inv_lt_inv₀ hε hδ).mpr hδε)
  have hcenter : N.center ∈ N.terminal_neck.carrier := by
    rw [← N.terminal_center]
    exact N.terminal_neck.central_sphere_subset N.terminal_neck.center_on_central_sphere
  have haxis : (N.terminal_neck.coordinate_inverse N.center).2 = 0 := by
    rw [← N.terminal_center]
    exact ((N.terminal_neck.mem_central_sphere_iff _).mp
      N.terminal_neck.center_on_central_sphere).2
  have haxis_cont : ContinuousAt (fun x => (N.terminal_neck.coordinate_inverse x).2) N.center :=
    (N.terminal_neck.coordinate_inverse_smooth.contMDiffAt
      (N.terminal_neck.carrier_open.mem_nhds hcenter)).continuousAt.snd
  have haxis_near : ∀ᶠ x in 𝓝 N.center,
      (N.terminal_neck.coordinate_inverse x).2 ∈ Ioo (-b) b :=
    haxis_cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds
      (by rw [haxis]; exact ⟨neg_lt_zero.mpr hb, hb⟩))
  have hcarrier_near : ∀ᶠ x in 𝓝 N.center, x ∈ N.terminal_neck.carrier :=
    N.terminal_neck.carrier_open.mem_nhds hcenter
  have hnear := hcarrier_near.and haxis_near
  have hproduct : ∀ᶠ p : ℕ × G.limit.carrier.carrier in atTop ×ˢ 𝓝 N.center,
      ∃ Q : StrongEvolvingNeck (S.term (G.subsequence p.1)).flow 0 ε,
        Q.center = ((e p.1).toFun (0, p.2)).2 := by
    filter_upwards [hfamily, hscalar.eventually (isOpen_Ioi.mem_nhds hR),
      tendsto_fst.eventually hstatic, tendsto_snd.eventually hnear]
      with p hpFamily hpR hpB hpNear
    obtain ⟨B, hBε, _, _, _, hBmap, _⟩ := hpB
    let q := (N.terminal_neck.coordinate_inverse p.2).1
    let s := (N.terminal_neck.coordinate_inverse p.2).2
    have hsub : MapsTo (fun t : ℝ => t + s)
        (Ioo (-ε⁻¹) ε⁻¹) (Ioo (-δ⁻¹) δ⁻¹) := by
      intro t ht
      have hs : -b < s ∧ s < b := hpNear.2
      dsimp only [b] at hs
      constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
    have hmap : B.coordinate_map (q, s) = ((e p.1).toFun (0, p.2)).2 := by
      rw [hBmap, G.terminalNeckEmbedding_apply]
      rw [show N.terminal_neck.coordinate_map (q, s) = p.2 from
        N.terminal_neck.coordinate_map_coordinate_inverse hpNear.1]
    obtain ⟨Q, hQ, _, _, _⟩ := CompactKappa.exists_strongNeck_of_translated_scalarFamily
      (S.term (G.subsequence p.1)).flow B hδ hδε.le hhalf
      (hBε.trans N.terminal_epsilon).le q s hsub
      (by rwa [hmap]) (by simpa only [hmap, hBmap, N.terminal_epsilon] using hpFamily)
    exact ⟨Q, hQ.trans hmap⟩
  obtain ⟨A, hA, V, hV, hAV⟩ := mem_prod_iff.mp hproduct
  obtain ⟨U, hUV, hUopen, hUc⟩ := mem_nhds_iff.mp hV
  refine ⟨U, hUopen, hUc, ?_⟩
  filter_upwards [hA] with k hk x hx
  have hmem : (k, x) ∈ A ×ˢ V := ⟨hk, hUV hx⟩
  exact hAV hmem

end M23TerminalMetricConvergence

end PoincareConjecture
