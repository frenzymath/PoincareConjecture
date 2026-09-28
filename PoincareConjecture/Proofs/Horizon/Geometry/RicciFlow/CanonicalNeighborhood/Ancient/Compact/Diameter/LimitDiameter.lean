import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalExtension

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}



theorem eventually_metricDiameter_le_of_compact
    (T : M23TerminalExtension G)
    (hcompact : IsCompact (univ : Set G.limit.carrier.carrier)) :
    ∀ᶠ k in atTop,
      metricDiameter ((S.term (G.subsequence k)).flow.flow.metric 0) univ ≤
        2 * metricDiameter (G.limit.flow.flow.metric 0) univ := by
  obtain ⟨e, _, _, hconv⟩ := T.terminal_embedding
  filter_upwards [G.eventually_exhaustion_eq_univ hcompact,
    hconv.eventually_inner_le_twice_on_compact hcompact] with k hk hmetric
  let f := fun x ↦ ((e k).toFun (0, x)).2
  let g := G.limit.flow.flow.metric 0
  let h := (S.term (G.subsequence k)).flow.flow.metric 0
  have hf : ContMDiff (𝓡 3) (𝓡 3) 1 f := fun x ↦
    ((e k).spatial_contMDiffAt (G.exhaustion_open k)
      (mem_Iic.mpr le_rfl) (hk ▸ mem_univ x)).of_le (by simp)
  have hsurj : Function.Surjective f :=
    (e k).spatial_surjective_of_compact hk hcompact (mem_Iic.mpr le_rfl)
  have hdist (x y : G.limit.carrier.carrier) :
      (h.edist (f x) (f y)).toReal ≤ 2 * (g.edist x y).toReal := by
    have hb : ∀ x v, h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ (2 : ℝ) ^ 2 * g.inner x v v := by
      intro x v
      have hinner := hmetric x (mem_univ x) v
      have hnonneg : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (g.pos x v hv).le
      change h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ 2 * g.inner x v v at hinner
      nlinarith
    have he := g.edist_le_mul_of_inner_mfderiv_le h hf (by norm_num : (0 : ℝ) < 2) hb x y
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g.edist_ne_top x y)) he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using hr
  apply csSup_le (range_nonempty _)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  obtain ⟨a, ha⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  change (h.edist x y).toReal ≤ _
  rw [← ha, ← hb]
  exact (hdist a b).trans (mul_le_mul_of_nonneg_left
    (compact_toReal_edist_le_metricDiameter g hcompact a b) (by norm_num))



theorem not_isCompact_of_metricDiameter_tendsto
    (T : M23TerminalExtension G)
    (hdiam : Tendsto (fun k ↦ metricDiameter ((S.term k).flow.flow.metric 0) univ)
      atTop atTop) :
    ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
  intro hcompact
  have hlarge := (hdiam.comp G.subsequence_strictMono.tendsto_atTop).eventually_gt_atTop
    (2 * metricDiameter (G.limit.flow.flow.metric 0) univ)
  obtain ⟨k, hupper, hlower⟩ :=
    ((T.eventually_metricDiameter_le_of_compact hcompact).and hlarge).exists
  exact (not_lt_of_ge hupper) hlower

end M23TerminalExtension

namespace RedesignNormalizedKappaCompactnessConclusion



theorem not_isCompact_of_metricDiameter_tendsto
    {N : NormalizedKappaCompactnessData}
    (L : RedesignNormalizedKappaCompactnessConclusion N)
    (hdiam : Tendsto (fun k ↦ metricDiameter ((N.sequence.term k).flow.flow.metric 0) univ)
      atTop atTop) :
    ¬ IsCompact (univ : Set L.convergence.limit.carrier.carrier) :=
  L.terminal_extension.not_isCompact_of_metricDiameter_tendsto hdiam

end RedesignNormalizedKappaCompactnessConclusion

end PoincareConjecture
