import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapLocalFlux
import PoincareConjecture.Proofs.M60.Mathlib.SecondLogDerivative
import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import PoincareConjecture.Proofs.M60.Mathlib.IntegralRegularization
import PoincareConjecture.Proofs.M04.ScalarEstimates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

private theorem annulus_second_fderiv_log_add
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






theorem m64Annulus_log_add_laplacian_lower_bound
    {a : LoopPlane → ℝ} {O : Set LoopPlane} {p : LoopPlane} {K ε : ℝ}
    (hO : IsOpen O) (hp : p ∈ O) (ha : ContDiffOn ℝ ∞ a O)
    (hnonneg : ∀ q ∈ O, 0 ≤ a q) (hK : 0 ≤ K) (hε : 0 < ε)
    (hregular : 0 < a p →
      ((fderiv ℝ a p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2 +
          (fderiv ℝ a p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) / a p -
        2 * K * (a p) ^ 2 ≤
      fderiv ℝ (fun q => fderiv ℝ a q (EuclideanSpace.single (0 : Fin 2) 1)) p
          (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ (fun q => fderiv ℝ a q (EuclideanSpace.single (1 : Fin 2) 1)) p
          (EuclideanSpace.single (1 : Fin 2) 1)) :
    -2 * K * a p ≤
      fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q
          (EuclideanSpace.single (0 : Fin 2) 1)) p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r + ε)) q
          (EuclideanSpace.single (1 : Fin 2) 1)) p
            (EuclideanSpace.single (1 : Fin 2) 1) := by
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hap : ContDiffAt ℝ ∞ a p := ha.contDiffAt (hO.mem_nhds hp)
  have hap2 : ContDiffAt ℝ 2 a p := hap.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpos : 0 < a p + ε := add_pos_of_nonneg_of_pos (hnonneg p hp) hε
  by_cases hpa : 0 < a p
  · rw [annulus_second_fderiv_log_add hap2 ε hpos.ne' b0,
      annulus_second_fderiv_log_add hap2 ε hpos.ne' b1]
    have hreg := hregular hpa
    have hraw := M60.log_regularization_inequality
      (a := a p) (ε := ε) (b :=
        fderiv ℝ (fun q => fderiv ℝ a q b0) p b0 +
          fderiv ℝ (fun q => fderiv ℝ a q b1) p b1)
      (c := 1 + K * a p)
      (q := (fderiv ℝ a p b0) ^ 2 + (fderiv ℝ a p b1) ^ 2)
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
    have hnonneg := D.laplacian_nonneg_of_isLocalMin
      (contMDiffAt_iff_contDiffAt.mpr hlog) hmin
    rw [D.laplacian_euclideanMetric hlog, Fin.sum_univ_two] at hnonneg
    rw [M60.fderiv_column (hlog.of_le (WithTop.coe_le_coe.mpr le_top)) b0 b0,
      M60.fderiv_column (hlog.of_le (WithTop.coe_le_coe.mpr le_top)) b1 b1]
    simpa only [hz, mul_zero, EuclideanSpace.basisFun_apply] using hnonneg

end PoincareConjecture
