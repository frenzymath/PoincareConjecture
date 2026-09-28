import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingGradient
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRadiusLimit
import Mathlib.Topology.UniformSpace.UniformApproximation











set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Convolution SchwartzMap InnerProductSpace

namespace PoincareConjecture.M65Interior





theorem averagingValue_exists_uniform_limit
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    {S : Set LoopPlane} {Λ β R : ℝ} (hΛ : 0 ≤ Λ) (hβ : 0 < β) (hR : 0 < R)
    (hE : ∀ x ∈ S, ∀ r ∈ Ioc 0 R,
      (∫ z in closedBall x r, ∑ i : Fin 2, (d i z) ^ 2) ≤ Λ * r ^ (2 * β)) :
    ∃ (v : LoopPlane → ℝ) (K : ℝ), 0 < K ∧ ContinuousOn v S ∧
      TendstoUniformlyOn (fun r x => averagingValue u r x) v (𝓝[>] 0) S ∧
      ∀ x ∈ S, ∀ r ∈ Ioc 0 R, |averagingValue u r x - v x| ≤ K * r ^ β := by
  classical
  obtain ⟨C, hC, hD⟩ := averagingValue_derivatives_of_energy (β := β) hΛ
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hdiff (x : LoopPlane) (r : ℝ) (hr : 0 < r) :
      DifferentiableAt ℝ (fun s => averagingValue u s x) r := by
    have hj : DifferentiableAt ℝ
        (fun p : ℝ × LoopPlane => averagingValue u p.1 p.2) (r, x) :=
      (averagingValue_joint_contDiffAt hu hr x).differentiableAt (by simp)
    have ha : DifferentiableAt ℝ (fun s : ℝ => (s, x)) r :=
      differentiableAt_id.prodMk (differentiableAt_const x)
    have hout := hj.comp r ha
    exact hout
  have hex (x : LoopPlane) : ∃ a : ℝ, x ∈ S →
      Tendsto (fun r => averagingValue u r x) (𝓝[>] 0) (𝓝 a) ∧
      ∀ r ∈ Ioc 0 R, |averagingValue u r x - a| ≤ (C / β) * r ^ β := by
    by_cases hx : x ∈ S
    · obtain ⟨a, ha⟩ := exists_radius_limit hC.le hβ hR
        (fun r hr => hdiff x r hr.1)
        (fun r hr => (hD u d hw x r hr.1 (hE x hx r hr)).2)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose v hv using hex
  let K := C / β
  have hK : 0 < K := div_pos hC hβ
  have hp : Tendsto (fun r : ℝ => K * r ^ β) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using
      (tendsto_const_nhds.mul
        ((Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.mono_left
          nhdsWithin_le_nhds) :
        Tendsto (fun r : ℝ => K * r ^ β) (𝓝[>] 0) (𝓝 (K * 0 ^ β)))
  have hlim : TendstoUniformlyOn (fun r x => averagingValue u r x) v (𝓝[>] 0) S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Ioo_mem_nhdsGT hR, hp.eventually (gt_mem_nhds hε)] with r hr he x hx
    rw [Real.dist_eq, abs_sub_comm]
    exact ((hv x hx).2 r ⟨hr.1, hr.2.le⟩).trans_lt he
  refine ⟨v, K, hK, ?_, hlim, fun x hx => (hv x hx).2⟩
  apply hlim.continuousOn
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hc : Continuous (averagingValue u r) := by
    exact ((averagingKernel_hasCompactSupport hr).contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hu (averagingKernel_contDiff r)).continuous
  exact hc.continuousOn

end PoincareConjecture.M65Interior
