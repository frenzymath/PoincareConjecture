import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.SpacetimeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TimeGrowth








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.AncientRescalingSequence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



theorem reducedLength_in_centered_chart_le
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (k : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ e.source) (hcenter : e a = S.base k)
    {B : ℝ≥0} (hB : ∀ x ∈ Metric.closedBall a r, ∀ v : EuclideanSpace ℝ (Fin n),
      ((S.rescaling k).flow.metric (-τ)).tangentNorm (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball a r) :
    reducedLength K.flow 0 S.reference (e x) (S.scale k * τ) ≤
      (Real.sqrt ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹) +
        Real.sqrt (3 / τ) / 2 * B * r) ^ 2 := by
  have h := P.rescaled_sqrt_reducedLength_coordinates_abs_le S.reference (S.rescaling k)
    hτ e he hei hball hB hx (Metric.mem_ball_self hr)
  rw [hcenter] at h
  have hC : 0 ≤ Real.sqrt (3 / τ) / 2 * (B : ℝ) := by positivity
  have hbound := h.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hx).le hC)
  have hbase := Real.sqrt_le_sqrt (S.reducedLength_at_base_time_le P k hτ)
  have hsqrt : Real.sqrt (reducedLength K.flow 0 S.reference (e x) (S.scale k * τ)) ≤
      Real.sqrt ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹) +
        Real.sqrt (3 / τ) / 2 * B * r := by
    have := (le_abs_self _).trans hbound
    linarith
  have hsq := Real.sq_sqrt (P.reducedLength_pos S.reference (e x) (S.scale k * τ)
    (mul_pos (S.scale_pos k) hτ)).le
  nlinarith [Real.sqrt_nonneg (reducedLength K.flow 0 S.reference (e x) (S.scale k * τ))]



theorem reducedLength_centered_coordinates_uniformEquicontinuousOn
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (e : ℕ → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e k) (e k).source)
    (hei : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e k).symm (e k).target)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.closedBall a r ⊆ (e k).source)
    (hcenter : ∀ k, e k a = S.base k)
    {B : ℝ≥0} (hB : ∀ k τ, τ ∈ Icc α β → ∀ x ∈ Metric.closedBall a r,
      ∀ v : EuclideanSpace ℝ (Fin n),
        ((S.rescaling k).flow.metric (-τ)).tangentNorm (e k x)
          (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤ B * ‖v‖) :
    UniformEquicontinuousOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
        reducedLength K.flow 0 S.reference (e k z.1) (S.scale k * z.2))
      (Metric.ball a r ×ˢ Icc α β) := by
  apply P.rescaled_reducedLength_coordinates_uniformEquicontinuousOn S hα e he hei
    (A := (Real.sqrt ((n : ℝ) / 2 * max (β ^ 2) (β ^ 2)⁻¹) +
      Real.sqrt (3 / β) / 2 * B * r) ^ 2) (sq_nonneg _) hball hB
  intro k x hx
  exact S.reducedLength_in_centered_chart_le P k (hα.trans_le hαβ) (e k) (he k) (hei k)
    hr (hball k) (hcenter k) (hB k β ⟨hαβ, le_rfl⟩) hx

end PoincareConjecture.AncientRescalingSequence
