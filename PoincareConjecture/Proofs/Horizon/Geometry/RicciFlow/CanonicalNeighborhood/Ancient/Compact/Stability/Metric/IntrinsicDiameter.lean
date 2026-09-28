import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.CompactCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Distance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture


theorem RiemannianMetric.intrinsicDiameter_image_le_of_tangentNorm_le
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f U)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ C * g.tangentNorm z v) :
    intrinsicDiameter h (f '' U) ≤ ENNReal.ofReal C * intrinsicDiameter g U := by
  apply sSup_le
  rintro _ ⟨⟨x, y⟩, rfl⟩
  obtain ⟨a, ha, hax⟩ := x.property
  obtain ⟨b, hb, hby⟩ := y.property
  change intrinsicEDist h (f '' U) x y ≤ _
  rw [← hax, ← hby]
  apply (g.intrinsicEDist_image_le_of_tangentNorm_le h hU hf
    (fun _ hz => mem_image_of_mem f hz) hC hbound a b).trans
  have hdiam : intrinsicEDist g U a b ≤ intrinsicDiameter g U :=
    le_sSup ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  exact mul_le_mul_right hdiam _

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}


theorem eventually_cap_intrinsicDiameter_le_twice
    (hconv : M23TerminalMetricConvergence G e)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      intrinsicDiameter ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x => ((e k).toFun (0, x)).2) '' A.carrier) ≤
        ENNReal.ofReal 2 * intrinsicDiameter (G.limit.flow.flow.metric 0) A.carrier := by
  have hcompact := A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [hconv.eventually_inner_le_twice_on_compact hcompact,
    eventually_ge_atTop j] with k hk hkj
  let f := fun x => ((e k).toFun (0, x)).2
  have hsub : A.carrier ⊆ G.exhaustion k :=
    fun _ hx => hmono hkj (hj (subset_closure hx))
  apply (G.limit.flow.flow.metric 0).intrinsicDiameter_image_le_of_tangentNorm_le
    ((S.term (G.subsequence k)).flow.flow.metric 0) A.carrier_open
    (fun x hx => ((e k).spatial_contMDiffAt (G.exhaustion_open k) (mem_Iic.mpr le_rfl)
      (hsub hx)).contMDiffWithinAt.of_le (by simp)) (by norm_num : (0 : ℝ) < 2)
  intro x hx v
  have hb := hk x (subset_closure hx) v
  have hnonneg : 0 ≤ (G.limit.flow.flow.metric 0).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((G.limit.flow.flow.metric 0).pos x v hv).le
  have hb' : ((S.term (G.subsequence k)).flow.flow.metric 0).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        2 ^ 2 * (G.limit.flow.flow.metric 0).inner x v v := by
    change ((S.term (G.subsequence k)).flow.flow.metric 0).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        2 * (G.limit.flow.flow.metric 0).inner x v v at hb
    linarith
  have h := Real.sqrt_le_sqrt hb'
  rw [Real.sqrt_mul (sq_nonneg (2 : ℝ)), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact h

end M23TerminalMetricConvergence

end PoincareConjecture
