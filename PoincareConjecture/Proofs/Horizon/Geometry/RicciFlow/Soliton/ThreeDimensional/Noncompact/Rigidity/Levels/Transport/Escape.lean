import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Shift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.PotentialLevels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Regularity.Potential


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem normalizedGradient_curve_centers_escape
    (S : GradientShrinkingSolitonData 3 M) {a : ℝ}
    (ha : ∀ x : M, a < S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (S.connection.boundedNormalizedGradient S.potential))
    (hstart : a < S.potential (γ 0)) (p : M) :
    Tendsto (fun k : ℕ => (S.metric.edist p (γ k)).toReal) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  let K := {x : M | S.metric.edist p x ≤ ENNReal.ofReal R}
  have hK : IsCompact K := S.metric.isCompact_closedBall_of_metricComplete S.complete p R
  obtain ⟨B, hB⟩ := hK.bddAbove_image S.potential_C2.continuous.continuousOn
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop
    (B - S.potential (γ 0))] with k hk
  by_contra hnot
  have hmem : γ (k : ℝ) ∈ K := by
    change S.metric.edist p (γ (k : ℝ)) ≤ ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal (S.metric.edist_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (lt_of_not_ge hnot).le
  have hupper := hB (mem_image_of_mem _ hmem)
  have heq := S.connection.potential_boundedNormalizedGradient_eq_add
    S.potential_contMDiff hγ ha hstart
    (show a < S.potential (γ 0) + (k : ℝ) from
      hstart.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg k)))
  linarith

theorem potential_normalizedGradient_flow_nat
    (S : GradientShrinkingSolitonData 3 M) {a : ℝ}
    (ha : ∀ x : M, a < S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x)
      (S.connection.boundedNormalizedGradient S.potential))
    {x : M} (hx : a < S.potential x) (k : ℕ) :
    S.potential (Φ (k : ℝ) x) = S.potential x + (k : ℝ) := by
  have hstart : a < S.potential (Φ 0 x) := by rwa [h0]
  have heq := S.connection.potential_boundedNormalizedGradient_eq_add
    S.potential_contMDiff (hΦ x) ha hstart
    (show a < S.potential (Φ 0 x) + (k : ℝ) from
      hstart.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg k)))
  simpa only [h0] using heq



theorem normalizedGradient_flow_between_centers
    (S : GradientShrinkingSolitonData 3 M) {a : ℝ}
    (ha : ∀ x : M, a < S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x)
      (S.connection.boundedNormalizedGradient S.potential))
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    {x : M} (hx : a < S.potential x) (i j : ℕ) :
    Φ (S.potential (Φ (j : ℝ) x) - S.potential (Φ (i : ℝ) x)) (Φ (i : ℝ) x) =
      Φ (j : ℝ) x := by
  rw [S.potential_normalizedGradient_flow_nat ha h0 hΦ hx j,
    S.potential_normalizedGradient_flow_nat ha h0 hΦ hx i, ← hadd]
  congr 1
  ring

end PoincareConjecture.GradientShrinkingSolitonData
