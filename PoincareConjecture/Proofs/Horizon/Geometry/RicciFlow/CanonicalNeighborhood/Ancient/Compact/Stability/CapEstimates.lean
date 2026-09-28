import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Supremum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.IntrinsicDiameter











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

private theorem scalarSup_image
    {M N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (D : LeviCivitaData g) (f : M → N) (U : Set M) :
    scalarCurvatureSupOn g D (f '' U) =
      sSup (range (fun x : U => D.scalarCurvature (f x))) := by
  unfold scalarCurvatureSupOn
  congr 1
  ext r
  constructor
  · rintro ⟨⟨y, hy⟩, hr⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, hr⟩
  · rintro ⟨x, hr⟩
    exact ⟨⟨f x, mem_image_of_mem f x.property⟩, hr⟩

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}


theorem tendstoUniformlyOn_cap_scalarCurvature
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    TendstoUniformlyOn (fun k x =>
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, x)).2) A.connection.scalarCurvature atTop A.carrier := by
  have h := (hconv.tendstoUniformlyOn_terminal_scalarCurvature hfixed
    (A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl))).mono subset_closure
  have heq : A.connection.scalarCurvature =
      (G.limit.flow.flow.connection 0).scalarCurvature :=
    funext (A.connection.scalarCurvature_eq (G.limit.flow.flow.connection 0))
  rwa [heq]


theorem tendsto_cap_scalarSup
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    Tendsto (fun k => scalarCurvatureSupOn
      ((S.term (G.subsequence k)).flow.flow.metric 0)
      ((S.term (G.subsequence k)).flow.flow.connection 0)
      ((fun x => ((e k).toFun (0, x)).2) '' A.carrier)) atTop
      (𝓝 (scalarCurvatureSupOn (G.limit.flow.flow.metric 0) A.connection A.carrier)) := by
  simpa only [scalarSup_image] using
    A.scalar_sup_tendsto (hconv.tendstoUniformlyOn_cap_scalarCurvature hfixed A)


theorem eventually_cap_scalar_pos_and_ratio
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      (∀ x ∈ (fun x => ((e k).toFun (0, x)).2) '' A.carrier,
        0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature x) ∧
      ∃ b : ℝ, b < A.cap_constant ∧
        ∀ x ∈ (fun x => ((e k).toFun (0, x)).2) '' A.carrier,
        ∀ y ∈ (fun x => ((e k).toFun (0, x)).2) '' A.carrier,
          ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature y ≤
            b * ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature x := by
  filter_upwards [A.eventually_scalar_pos_and_ratio
    (hconv.tendstoUniformlyOn_cap_scalarCurvature hfixed A)] with k hk
  refine ⟨?_, hk.2.choose, hk.2.choose_spec.1, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hk.1 x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hk.2.choose_spec.2 x hx y hy



theorem eventually_cap_intrinsic_diameter_bound
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      intrinsicDiameter ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x => ((e k).toFun (0, x)).2) '' A.carrier) <
        ENNReal.ofReal (4 * A.cap_constant *
          (scalarCurvatureSupOn ((S.term (G.subsequence k)).flow.flow.metric 0)
            ((S.term (G.subsequence k)).flow.flow.connection 0)
            ((fun x => ((e k).toFun (0, x)).2) '' A.carrier)) ^ (-1 / 2 : ℝ)) := by
  let R := scalarCurvatureSupOn (G.limit.flow.flow.metric 0) A.connection A.carrier
  have hR : 0 < R ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos A.scalar_sup_pos _
  have ht := (hconv.tendsto_cap_scalarSup hfixed A).rpow_const
    (p := (-1 / 2 : ℝ)) (Or.inl A.scalar_sup_pos.ne')
  have hlower := ht.eventually (lt_mem_nhds (half_lt_self hR))
  filter_upwards [hconv.eventually_cap_intrinsicDiameter_le_twice A, hlower] with k hk hscale
  apply hk.trans_lt
  have hstrict := ENNReal.mul_right_strictMono
    (by norm_num : ENNReal.ofReal 2 ≠ 0) ENNReal.ofReal_ne_top A.intrinsic_diameter_bound
  apply hstrict.trans_le
  dsimp only
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  have hmul := mul_le_mul_of_nonneg_left hscale.le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) A.cap_constant_pos.le)
  change 2 * (A.cap_constant * R ^ (-1 / 2 : ℝ)) ≤ _
  nlinarith

end M23TerminalMetricConvergence

end PoincareConjecture
