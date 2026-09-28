import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallScalarLimit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem tubeCritical_base_scalar_eq (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1) (k : ℕ)
    (D : LeviCivitaData (H.tubeCriticalMetric T A1 k)) :
    D.scalarCurvature (H.tubeCriticalBase T A1 hA1 k) = 16 * (max C 2) ^ 2 := by
  rw [H.tubeCritical_scalar_eq T A1 k D]
  change (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ = _
  rw [(H.segment k).lower_scalar]
  exact mul_div_cancel_right₀ _ (H.base_scalar_pos k).ne'

set_option maxHeartbeats 2400000 in

theorem regular_limit_base_scalar_eq (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ D₀ : LeviCivitaData G.limitMetric,
      D₀.scalarCurvature G.base = 16 * (max C 2) ^ 2 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  let D (k : ℕ) : LeviCivitaData (H.tubeCriticalMetric T A1 (phi k)) :=
    Classical.choice (exists_leviCivitaData (H.tubeCriticalMetric T A1 (phi k)))
  have hlimit := G.tendsto_scalarCurvature D D₀ G.base
  have heq : (fun k => (D (G.subsequence k)).scalarCurvature (G.embedding k G.base)) =
      (fun _ : ℕ => 16 * (max C 2) ^ 2) := by
    funext k
    rw [G.base_preserving]
    exact H.tubeCritical_base_scalar_eq T A1 hA1 (phi (G.subsequence k)) _
  rw [heq] at hlimit
  exact tendsto_nhds_unique hlimit tendsto_const_nhds

set_option maxHeartbeats 2400000 in

theorem regular_limit_base_scale_eq (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ D₀ : LeviCivitaData G.limitMetric,
      0 < D₀.scalarCurvature G.base ∧
        (D₀.scalarCurvature G.base) ^ (-1 / 2 : ℝ) = (4 * max C 2)⁻¹ := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  rw [H.regular_limit_base_scalar_eq T A1 hA1 phi G D₀]
  have hC : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  refine ⟨by positivity, ?_⟩
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (by positivity : 0 ≤ 16 * (max C 2) ^ 2), ← Real.sqrt_eq_rpow]
  rw [show 16 * (max C 2) ^ 2 = (4 * max C 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity : 0 ≤ 4 * max C 2)]

end PoincareConjecture.M28.CounterexampleNeckFamily
