import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerChartBounds
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalHolder












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Euler

set_option maxHeartbeats 1800000 in





theorem exists_chart_energy_decay {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {U V : Set LoopPlane} (hU : IsOpen U) (hV : IsOpen V)
    (F : M65LocalWeakMap e U) (hmin : M65LocallyMinimizesEnergy g F)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) V)
    (q : LoopPlane → M) (hqcont : ContinuousOn q U)
    (hq : q =ᵐ[volume.restrict U] F.value) {x : LoopPlane} (hxU : x ∈ U) (hxV : x ∈ V)
    (hX : ∀ z ∈ V, X.value z = extChartAt (𝓡 3) (q x) (q z)) :
    ∃ r β Λ : ℝ, 0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < Λ ∧ closedBall x r ⊆ V ∧
      ∀ y ∈ closedBall x (r / 2), ∀ s : ℝ, 0 < s → s ≤ r / 2 →
        (∫ z in closedBall y s, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
          Λ * s ^ (2 * β) := by
  obtain ⟨r, hr, h4, H, C, _hH, hC, _hLip, _hvalue, hfield⟩ :=
    exists_chart_field_transfer e he hinj hU hV F X q hqcont hq hxU hxV hX
  have h1U : closedBall x r ⊆ U :=
    ((closedBall_subset_closedBall (by linarith)).trans h4).trans inter_subset_left
  have h1V : closedBall x r ⊆ V :=
    ((closedBall_subset_closedBall (by linarith)).trans h4).trans inter_subset_right
  obtain ⟨β, Λ, hβ, hβ1, hΛ, hdecay⟩ :=
    F.local_derivative_energy_decay g he hinj hemb compact hU hmin x hr h1U
  refine ⟨r, β, 1 + (C : ℝ) ^ 2 * Λ, hr, hβ, hβ1, by positivity, h1V, ?_⟩
  intro y hy s hs hsr
  have hsub : closedBall y s ⊆ closedBall x r := closedBall_subset_closedBall' (by
    have hy' : dist y x ≤ r / 2 := hy
    linarith)
  have hsub2 : closedBall y s ⊆ ball x (2 * r) :=
    hsub.trans (closedBall_subset_ball (by linarith))
  have hXi : IntegrableOn (fun z => ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2)
      (closedBall y s) := by
    apply integrable_finsetSum
    intro i _
    exact (X.derivative_memLp i (closedBall y s) (isCompact_closedBall _ _)
      (hsub.trans h1V)).norm.integrable_sq
  have hFi : IntegrableOn (fun z => ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2)
      (closedBall y s) := by
    apply integrable_finsetSum
    intro i _
    exact (F.derivative_memLp i (closedBall y s) (isCompact_closedBall _ _)
      (hsub.trans h1U)).norm.integrable_sq
  have hpoint : ∀ᵐ z ∂volume.restrict (closedBall y s),
      (∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        (C : ℝ) ^ 2 * ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub2 (ae_all_iff.mpr hfield)]
      with z hz
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hz i]
    have hn : ‖fderiv ℝ H (e (q z)) (F.derivative i z)‖ ≤ (C : ℝ) * ‖F.derivative i z‖ :=
      ((fderiv ℝ H (e (q z))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hbound := integral_mono_ae hXi (hFi.const_mul ((C : ℝ) ^ 2)) hpoint
  rw [integral_const_mul] at hbound
  calc
    _ ≤ (C : ℝ) ^ 2 * ∫ z in closedBall y s, ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2 := hbound
    _ ≤ (C : ℝ) ^ 2 * (Λ * s ^ (2 * β)) :=
      mul_le_mul_of_nonneg_left (hdecay y hy s hs hsr) (sq_nonneg _)
    _ ≤ (1 + (C : ℝ) ^ 2 * Λ) * s ^ (2 * β) := by
      nlinarith [Real.rpow_nonneg hs.le (2 * β)]

end PoincareConjecture.M65Euler
