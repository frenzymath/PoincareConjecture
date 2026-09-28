import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.EmbeddingBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactness

theorem tendsto_of_compact_zero_jets
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℕ → X → Y) (B : X → Y) (Ω : Set X)
    (hzero : ∀ K : Set X, IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn (fun k => iteratedFDerivWithin ℝ 0 (f k) Ω)
        (iteratedFDerivWithin ℝ 0 B Ω) atTop K)
    {z : X} (hz : z ∈ Ω) : Tendsto (fun k => f k z) atTop (𝓝 (B z)) := by
  have hjet := hzero {z} isCompact_singleton (singleton_subset_iff.mpr hz)
  have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → X)).comp_tendstoUniformlyOn hjet
  simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
    hvalue.tendsto_at (mem_singleton z)

private theorem tendsto_bilinear_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (h : Tendsto f atTop (𝓝 B)) (v w : E) :
    Tendsto (fun k => f k v w) atTop (𝓝 (B v w)) :=
  ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto (B v)).comp
    (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.tendsto B).comp h)

end PoincareConjecture.AncientCompactness

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalPositivityCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

theorem terminal_coefficients_symmetric_positive
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (B : ℝ × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hconv : ∀ t : ℝ, t ≤ 0 → ∀ x ∈ K,
      Tendsto (fun k => ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
        (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x) atTop (𝓝 (B (t, x)))) :
    (∀ t : ℝ, t ≤ 0 → ∀ x ∈ K, ∀ v w, B (t, x) v w = B (t, x) w v) ∧
    (∀ t : ℝ, t ≤ 0 → ∀ x ∈ K, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v) := by
  constructor
  · intro t ht x hx v w
    have hvw := AncientCompactness.tendsto_bilinear_eval (hconv t ht x hx) v w
    have hwv := AncientCompactness.tendsto_bilinear_eval (hconv t ht x hx) w v
    have heq : (fun k : ℕ => ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
        (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x v w) =
        (fun k : ℕ => ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x w v) := by
      funext k
      exact ((S.term (G.subsequence k)).flow.flow.metric t).symm _ _ _
    rw [heq] at hvw
    exact tendsto_nhds_unique hvw hwv
  · intro t ht x hx
    obtain ⟨a, b, ha, _, hbound⟩ := S.exists_eventually_embedding_closed_ellipticity
      G P hcontrol hcomplete q hK hKc (le_max_left 1 (-t))
    have htime : t ∈ Icc (-max 1 (-t)) 0 := ⟨by linarith [le_max_right 1 (-t)], ht⟩
    refine ⟨a, ha, fun v => ?_⟩
    apply ge_of_tendsto (AncientCompactness.tendsto_bilinear_eval (hconv t ht x hx) v v)
    exact hbound.mono fun k hk => (hk t htime x hx v).1

theorem terminal_coefficients_symmetric_positive_of_zero_jets
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    (B : ℝ × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hzero : ∀ A : Set (ℝ × EuclideanSpace ℝ (Fin 3)), IsCompact A →
      A ⊆ Iic 0 ×ˢ K → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ 0
          (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
              (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2) (Iic 0 ×ˢ K))
        (iteratedFDerivWithin ℝ 0 B (Iic 0 ×ˢ K)) atTop A) :
    (∀ t : ℝ, t ≤ 0 → ∀ x ∈ K, ∀ v w, B (t, x) v w = B (t, x) w v) ∧
    (∀ t : ℝ, t ≤ 0 → ∀ x ∈ K, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v) := by
  apply S.terminal_coefficients_symmetric_positive G P hcontrol hcomplete q hK hKc B
  intro t ht x hx
  exact AncientCompactness.tendsto_of_compact_zero_jets _ B (Iic 0 ×ˢ K) hzero
    (z := (t, x)) ⟨show t ∈ Iic 0 from ht, hx⟩

end PoincareConjecture.NormalizedKappaSolutionSequence
