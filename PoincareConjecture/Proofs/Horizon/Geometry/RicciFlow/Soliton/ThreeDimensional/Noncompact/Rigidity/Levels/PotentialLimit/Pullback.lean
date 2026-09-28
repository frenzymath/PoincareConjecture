import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Source
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.AtInfinity.UnscaledLimit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

def unscaledOriginalEmbedding (k : ℕ) (x : L.limitCarrier.carrier) : M :=
  (equivShrink M).symm (L.embedding k x)

def normalizedPotentialPullback (k : ℕ) (x : L.limitCarrier.carrier) : ℝ :=
  S.normalizedPotential (q (L.subsequence k)) (G.unscaledOriginalEmbedding L k x)

theorem unscaledOriginalEmbedding_base (k : ℕ) :
    G.unscaledOriginalEmbedding L k L.base = q (L.subsequence k) := by
  simp only [unscaledOriginalEmbedding, L.base_preserving, Equiv.symm_apply_apply]

@[simp] theorem normalizedPotentialPullback_base (k : ℕ) :
    G.normalizedPotentialPullback L k L.base = 0 := by
  rw [normalizedPotentialPullback, G.unscaledOriginalEmbedding_base,
    S.normalizedPotential_center]

theorem unscaledOriginalEmbedding_contMDiffOn (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (G.unscaledOriginalEmbedding L k) (L.exhaustion k) := by
  exact (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M).symm.contMDiff.comp_contMDiffOn
    (L.embedding_smooth k).contMDiffOn

theorem normalizedPotentialPullback_contMDiffOn (k : ℕ) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (G.normalizedPotentialPullback L k) (L.exhaustion k) :=
  (S.normalizedPotential_contMDiff (q (L.subsequence k))).comp_contMDiffOn
    (G.unscaledOriginalEmbedding_contMDiffOn L k)

theorem unscaledOriginalEmbedding_inner (k : ℕ) (x : L.limitCarrier.carrier)
    (hx : x ∈ L.exhaustion k) (v w : TangentSpace (𝓡 3) x) :
    S.metric.inner (G.unscaledOriginalEmbedding L k x)
      (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v)
      (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x w) =
      spatialPullbackInner L.limitCarrier
        (AncientRescalingSequence.smallRescalingCarrier (M := M))
        (G.unscaledSourceFlow.shrink.metric 0) (L.embedding k) x v w := by
  let d := (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M).symm
  have hd := mfderiv_comp x (d.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (((L.embedding_smooth k).contMDiffOn.contMDiffAt
      ((L.exhaustion_open k).mem_nhds hx)).mdifferentiableAt (by simp))
  change S.metric.inner (d (L.embedding k x))
    (mfderiv (𝓡 3) (𝓡 3) (d ∘ L.embedding k) x v)
    (mfderiv (𝓡 3) (𝓡 3) (d ∘ L.embedding k) x w) = _
  rw [hd]
  change S.metric.inner _ _ _ = (G.unscaledSourceFlow.metric 0).inner _ _ _
  rw [G.unscaledSourceFlow_metric_zero]
  rfl

theorem normalizedPotentialPullback_scale_tendsto_atTop
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop) :
    Tendsto (fun k => S.potentialGradientScale (q (L.subsequence k))) atTop atTop :=
  (S.potentialGradientScale_tendsto_atTop_of_escape hD p q hescape).comp
    L.subsequence_strictMono.tendsto_atTop

theorem normalizedPotentialPullback_hessian_eventually_lt
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (j : ℕ) (K : Set L.limitCarrier.carrier) (hK : IsCompact K)
    (hKj : K ⊆ L.exhaustion j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      L.limitCarrier.metricNorm (L.limitFlow.metric 0) x v ≤ 1 →
      |S.connection.hessian (S.normalizedPotential (q (L.subsequence k)))
        (G.unscaledOriginalEmbedding L k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v)
        (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v)| < ε := by
  obtain ⟨C, hC, hbound⟩ := S.exists_normalizedPotential_hessian_bound
  have ha := G.normalizedPotentialPullback_scale_tendsto_atTop L hD p hescape
  obtain ⟨N, hjN, hmetric⟩ := L.pullback_metric_converges j K {0} hK hKj
    isCompact_singleton (by simp) 1 (by norm_num)
  have hmono : Monotone L.exhaustion := monotone_nat_of_le_succ L.exhaustion_increasing
  filter_upwards [ha.eventually_gt_atTop (2 * C / ε + 1), eventually_ge_atTop N]
    with k hk hkN
  have hscale : 0 < S.potentialGradientScale (q (L.subsequence k)) := by
    have hnonneg : 0 ≤ 2 * C / ε := by positivity
    linarith
  have hsmall : 2 * (C / S.potentialGradientScale (q (L.subsequence k))) < ε := by
    have hlt : 2 * C / ε < S.potentialGradientScale (q (L.subsequence k)) := by linarith
    have hm := (div_lt_iff₀ hε).mp hlt
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ hscale).mpr (by nlinarith)
  intro x hx v hv
  have hxk : x ∈ L.exhaustion k := hmono (hjN.trans hkN) (hKj hx)
  have hmet := hmetric k hkN 0 (mem_singleton 0) x hx v v hv hv
  rw [← G.unscaledOriginalEmbedding_inner L k x hxk v v] at hmet
  have hlim : L.limitCarrier.metricInner (L.limitFlow.metric 0) x v v ≤ 1 := by
    have hnonneg : 0 ≤ L.limitCarrier.metricInner (L.limitFlow.metric 0) x v v := by
      change 0 ≤ (L.limitFlow.metric 0).inner x v v
      by_cases hz : v = 0
      · simp [hz]
      · exact ((L.limitFlow.metric 0).pos x v hz).le
    have hs := Real.sq_sqrt hnonneg
    change L.limitCarrier.metricNorm (L.limitFlow.metric 0) x v ^ 2 = _ at hs
    have hn : 0 ≤ L.limitCarrier.metricNorm (L.limitFlow.metric 0) x v :=
      Real.sqrt_nonneg _
    nlinarith
  have hsource : S.metric.inner (G.unscaledOriginalEmbedding L k x)
      (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v)
      (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v) ≤ 2 := by
    have h := (abs_lt.mp hmet).2
    linarith
  exact (hbound _ _ _).trans_lt
    ((mul_le_mul_of_nonneg_left hsource (div_nonneg hC hscale.le)).trans_lt
      (by simpa only [mul_comm] using hsmall))

end PoincareConjecture.ShrinkingSolitonFlow
