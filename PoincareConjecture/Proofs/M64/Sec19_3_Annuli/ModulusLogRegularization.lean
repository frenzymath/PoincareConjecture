import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusLogRegularization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

private theorem modulus_second_fderiv_log_add
    {a : LoopPlane → ℝ} {p : LoopPlane} (ha : ContDiffAt ℝ 2 a p)
    (ε : ℝ) (hpos : a p + ε ≠ 0) (v : LoopPlane) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ a q v) p v / (a p + ε) -
        (fderiv ℝ a p v) ^ 2 / (a p + ε) ^ 2 := by
  have hfirst : (fun q => fderiv ℝ (fun r => a r + ε) q v) =ᶠ[𝓝 p]
      fun q => fderiv ℝ a q v := by
    filter_upwards [ha.eventually (by norm_num)] with q hq
    rw [((hq.differentiableAt (by norm_num)).hasFDerivAt.add_const ε).fderiv]
  have hfirstp := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L v)
    ((ha.differentiableAt (by norm_num)).hasFDerivAt.add_const ε).fderiv
  rw [M60.second_fderiv_log (ha.add contDiffAt_const) hpos v,
    hfirst.fderiv_eq, hfirstp]

theorem m64Modulus_log_add_directional_lower_bound
    {a : LoopPlane → ℝ} {O : Set LoopPlane} {p : LoopPlane} {K ε : ℝ}
    (d e : LoopPlane) (hO : IsOpen O) (hp : p ∈ O) (ha : ContDiffOn ℝ ∞ a O)
    (hnonneg : ∀ q ∈ O, 0 ≤ a q) (hK : 0 ≤ K) (hε : 0 < ε)
    (hregular : 0 < a p →
      ((fderiv ℝ a p d) ^ 2 + (fderiv ℝ a p e) ^ 2) / a p -
        2 * K * (a p) ^ 2 ≤
      fderiv ℝ (fun q => fderiv ℝ a q d) p d +
        fderiv ℝ (fun q => fderiv ℝ a q e) p e) :
    -2 * K * a p ≤
      fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q d) p d +
        fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q e) p e := by
  have hap : ContDiffAt ℝ ∞ a p := ha.contDiffAt (hO.mem_nhds hp)
  have hap2 : ContDiffAt ℝ 2 a p := hap.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpos : 0 < a p + ε := add_pos_of_nonneg_of_pos (hnonneg p hp) hε
  by_cases hpa : 0 < a p
  · rw [modulus_second_fderiv_log_add hap2 ε hpos.ne' d,
      modulus_second_fderiv_log_add hap2 ε hpos.ne' e]
    have hreg := hregular hpa
    have hraw := M60.log_regularization_inequality
      (a := a p) (ε := ε) (b :=
        fderiv ℝ (fun q => fderiv ℝ a q d) p d +
          fderiv ℝ (fun q => fderiv ℝ a q e) p e)
      (c := 1 + K * a p)
      (q := (fderiv ℝ a p d) ^ 2 + (fderiv ℝ a p e) ^ 2)
      hpa hε (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by
        convert hreg using 1
        ring)
    have hbound : -2 * K * a p ≤ -2 * K * (a p) ^ 2 / (a p + ε) := by
      apply (le_div_iff₀ hpos).mpr
      nlinarith [mul_nonneg (mul_nonneg hK hpa.le) hε.le]
    calc
      -2 * K * a p ≤ -2 * K * (a p) ^ 2 / (a p + ε) := hbound
      _ ≤ _ := by convert hraw using 1 <;> ring
  · have hz : a p = 0 := le_antisymm (le_of_not_gt hpa) (hnonneg p hp)
    have hlog : ContDiffAt ℝ ∞ (fun q => Real.log (a q + ε)) p :=
      (hap.add contDiffAt_const).log hpos.ne'
    have hmin : IsLocalMin (fun q => Real.log (a q + ε)) p := by
      filter_upwards [hO.mem_nhds hp] with q hq
      rw [hz, zero_add]
      exact Real.strictMonoOn_log.monotoneOn hε
        (add_pos_of_nonneg_of_pos (hnonneg q hq) hε)
        (le_add_of_nonneg_left (hnonneg q hq))
    let D := (RiemannianMetric.euclideanMetric 2).euclideanLeviCivitaData
    have hdir (v : LoopPlane) : 0 ≤
        fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q v) p v := by
      have h := D.hessian_nonneg_of_isLocalMin
        (contMDiffAt_iff_contDiffAt.mpr hlog) hmin v
      rw [D.hessian_euclideanMetric hlog] at h
      rw [M60.fderiv_column (hlog.of_le (WithTop.coe_le_coe.mpr le_top)) v v]
      exact h
    simpa only [hz, mul_zero] using add_nonneg (hdir d) (hdir e)

theorem m64SecondDirectional_smul
    {f : LoopPlane → ℝ} {p : LoopPlane} (hf : ContDiffAt ℝ 2 f p)
    (c : ℝ) (d : LoopPlane) :
    fderiv ℝ (fun q => fderiv ℝ f q (c • d)) p (c • d) =
      c ^ 2 * fderiv ℝ (fun q => fderiv ℝ f q d) p d := by
  rw [M60.fderiv_column hf (c • d) (c • d), M60.fderiv_column hf d d]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end PoincareConjecture
