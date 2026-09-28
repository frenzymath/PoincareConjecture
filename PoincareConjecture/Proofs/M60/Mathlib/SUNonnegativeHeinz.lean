import PoincareConjecture.Proofs.M60.Mathlib.SUHeinzEstimate









noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60


theorem suPlaneLaplacian_add_const (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    suPlaneLaplacian (fun y => u y + c) x = suPlaneLaplacian u x := by
  have hd : fderiv ℝ (fun y => u y + c) = fderiv ℝ u :=
    funext fun _ => fderiv_add_const c
  simp only [suPlaneLaplacian, hd]



theorem exists_heinz_estimate :
    ∃ A : ℝ, 0 < A ∧ ∀ (K R : ℝ), 0 ≤ K → 0 < R → R ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ ∞ u → (∀ x, 0 ≤ u x) →
        (∀ x ∈ Metric.ball 0 R, -K * (u x) ^ 2 ≤ suPlaneLaplacian u x) →
        A * K * (∫ x in Metric.closedBall 0 R, u x) ≤ 1 →
        R ^ 2 * u 0 ≤ A * (∫ x in Metric.closedBall 0 R, u x) := by
  obtain ⟨A, hA, hest⟩ := exists_positive_heinz_estimate
  refine ⟨2 * A, by positivity, fun K R hK hR hR1 u hu hnonneg hlap hsmall => ?_⟩
  let S := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R
  let E : ℝ := ∫ x in S, u x
  let V : ℝ := volume.real S
  have hE : 0 ≤ E := integral_nonneg hnonneg
  have hiu : IntegrableOn u S volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) hu.continuous.continuousOn
  have hint (c : ℝ) : (∫ x in S, u x + c) = E + V * c := by
    have hic : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) => c) S volume :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) continuousOn_const
    rw [integral_add hiu hic, setIntegral_const, smul_eq_mul]
  have hsmall0 : A * K * (E + V * 0) < 1 := by
    change 2 * A * K * E ≤ 1 at hsmall
    simp only [mul_zero, add_zero]
    nlinarith only [hsmall]
  have hc : Continuous (fun c : ℝ => A * K * (E + V * c)) := by fun_prop
  have hev : ∀ᶠ c : ℝ in 𝓝[>] 0, A * K * (E + V * c) < 1 :=
    (hc.continuousAt.eventually (gt_mem_nhds hsmall0)).filter_mono nhdsWithin_le_nhds
  have hb : ∀ᶠ c : ℝ in 𝓝[>] 0,
      R ^ 2 * (u 0 + c) ≤ A * (E + V * c) := by
    filter_upwards [hev, self_mem_nhdsWithin] with c hc hcp
    have hcpos : 0 < c := hcp
    have huc : ContDiff ℝ ∞ (fun x => u x + c) := hu.add contDiff_const
    have hucpos (x : EuclideanSpace ℝ (Fin 2)) : 0 < u x + c := by
      linarith [hnonneg x]
    have hlc (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Metric.ball 0 R) :
        -K * (u x + c) ^ 2 ≤ suPlaneLaplacian (fun y => u y + c) x := by
      rw [suPlaneLaplacian_add_const]
      have hsq : (u x) ^ 2 ≤ (u x + c) ^ 2 := by nlinarith [hnonneg x]
      have hm := mul_le_mul_of_nonneg_left hsq hK
      nlinarith only [hlap x hx, hm]
    have hm := hest K R hK hR hR1 (fun x => u x + c) huc hucpos hlc
      (by rw [show Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R = S from rfl,
        hint]; exact hc.le)
    rw [show Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R = S from rfl, hint] at hm
    exact hm
  have hleft : Tendsto (fun c : ℝ => R ^ 2 * (u 0 + c)) (𝓝[>] 0)
      (𝓝 (R ^ 2 * u 0)) := by
    have hcont : Continuous (fun c : ℝ => R ^ 2 * (u 0 + c)) := by fun_prop
    simpa only [add_zero] using hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
  have hright : Tendsto (fun c : ℝ => A * (E + V * c)) (𝓝[>] 0) (𝓝 (A * E)) := by
    have hcont : Continuous (fun c : ℝ => A * (E + V * c)) := by fun_prop
    simpa only [mul_zero, add_zero] using hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
  have hle := le_of_tendsto_of_tendsto hleft hright hb
  change R ^ 2 * u 0 ≤ 2 * A * E
  nlinarith [mul_nonneg hA.le hE]

end PoincareConjecture.M60
