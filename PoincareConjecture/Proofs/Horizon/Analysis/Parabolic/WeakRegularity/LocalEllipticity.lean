import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import Mathlib.Topology.Order.Compact

open Set Metric
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

private theorem uniformlyEllipticOn_of_compact (C : Coefficients n)
    {K : Set (Spacetime n)} (hK : IsCompact K)
    (hC : ∀ i j, ContinuousOn (C.principal i j) K)
    (hpos : ∀ z ∈ K, ∀ ξ : Euclid n, ξ ≠ 0 →
      0 < ∑ i, ∑ j, C.principal i j z * ξ i * ξ j) :
    C.IsUniformlyEllipticOn K := by
  let Q : Spacetime n × Euclid n → ℝ :=
    fun z => ∑ i, ∑ j, C.principal i j z.1 * z.2 i * z.2 j
  let S := sphere (0 : Euclid n) 1
  have hKS : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere 0 1)
  have hQ : ContinuousOn Q (K ×ˢ S) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have hc : ContinuousOn (fun z : Spacetime n × Euclid n => C.principal i j z.1)
        (K ×ˢ S) :=
      (hC i j).comp continuous_fst.continuousOn (fun _ hz => hz.1)
    exact (hc.mul (by fun_prop)).mul (by fun_prop)
  obtain ⟨κ, hκ, hmin⟩ := hKS.exists_forall_le' hQ (a := 0) (by
    intro z hz
    apply hpos z.1 hz.1 z.2
    have hn : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    intro heq
    simp [heq] at hn)
  refine ⟨κ, hκ, ?_⟩
  intro z hz ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  · let η := ‖ξ‖⁻¹ • ξ
    have hη : η ∈ S := mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hξ)
    have hscale : ‖ξ‖ • η = ξ := by
      dsimp [η]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), one_smul]
    have hhom (c : ℝ) (v : Euclid n) : Q (z, c • v) = c ^ 2 * Q (z, v) := by
      simp only [Q, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hbound := mul_le_mul_of_nonneg_left (hmin (z, η) ⟨hz, hη⟩) (sq_nonneg ‖ξ‖)
    rw [← hhom, hscale] at hbound
    simpa only [Q, mul_comm] using hbound

theorem exists_uniformlyElliptic_closedBall {n : ℕ} {U : Set (Spacetime n)}
    (hU : IsOpen U) (C : Coefficients n) (hC : C.IsSmoothOn U)
    (hpos : ∀ z ∈ U, ∀ ξ : Euclid n, ξ ≠ 0 →
      0 < ∑ i, ∑ j, C.principal i j z * ξ i * ξ j)
    {z : Spacetime n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ U ∧
      C.IsUniformlyEllipticOn (Metric.closedBall z r) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hclosed : closedBall z (r / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  refine ⟨r / 2, half_pos hr, hclosed, ?_⟩
  exact uniformlyEllipticOn_of_compact C (isCompact_closedBall z (r / 2))
    (fun i j => (hC.1 i j).continuousOn.mono hclosed)
    (fun y hy => hpos y (hclosed hy))

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
