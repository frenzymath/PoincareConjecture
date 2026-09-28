import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateJacobian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarMetricEnergy














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ






theorem scalarCoverMap_radial_column (r t : ℝ) :
    fderiv ℝ scalarCoverMap (r, t) (1, 0) =
      Real.cos (2 * Real.pi * t) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        Real.sin (2 * Real.pi * t) • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  have h := (((hasDerivAt_id r).mul_const (Real.cos (2 * Real.pi * t))).smul_const
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)).add
      (((hasDerivAt_id r).mul_const (Real.sin (2 * Real.pi * t))).smul_const
        (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hactual :=
    (scalarCoverMap_smooth.differentiable (by simp) (r, t)).hasFDerivAt.comp_hasDerivAt
    r ((hasDerivAt_id r).prodMk (hasDerivAt_const r t))
  have hsimple : HasDerivAt (fun s : ℝ => scalarCoverMap (s, t))
      (Real.cos (2 * Real.pi * t) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        Real.sin (2 * Real.pi * t) • EuclideanSpace.basisFun (Fin 2) ℝ 1) r := by
    simpa only [scalarCoverMap, scalarCirclePoint, one_mul, Pi.add_apply, id_eq] using! h
  exact hactual.unique hsimple






theorem scalarCoverMap_angular_column (r t : ℝ) :
    fderiv ℝ scalarCoverMap (r, t) (0, 1) =
      (r * (-Real.sin (2 * Real.pi * t) * (2 * Real.pi))) •
        EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      (r * (Real.cos (2 * Real.pi * t) * (2 * Real.pi))) •
        EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  have ha : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
    simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul (2 * Real.pi)
  have h := ((((Real.hasDerivAt_cos (2 * Real.pi * t)).comp t ha).const_mul r).smul_const
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)).add
      ((((Real.hasDerivAt_sin (2 * Real.pi * t)).comp t ha).const_mul r).smul_const
        (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hsimple : HasDerivAt (scalarCirclePoint r)
      ((r * (-Real.sin (2 * Real.pi * t) * (2 * Real.pi))) •
        EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      (r * (Real.cos (2 * Real.pi * t) * (2 * Real.pi))) •
        EuclideanSpace.basisFun (Fin 2) ℝ 1) t := by
    simpa only [Function.comp_def, scalarCirclePoint, Pi.add_apply] using! h
  exact (scalarCirclePoint_hasDerivAt r t).unique hsimple







theorem scalarCoverMap_column_determinant (r t : ℝ) :
    (fderiv ℝ scalarCoverMap (r, t) (1, 0)) 0 *
        (fderiv ℝ scalarCoverMap (r, t) (0, 1)) 1 -
      (fderiv ℝ scalarCoverMap (r, t) (1, 0)) 1 *
        (fderiv ℝ scalarCoverMap (r, t) (0, 1)) 0 = 2 * Real.pi * r := by
  rw [scalarCoverMap_radial_column, scalarCoverMap_angular_column]
  simp only [EuclideanSpace.basisFun_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, PiLp.single_apply,
    Fin.zero_eq_one_iff, Fin.reduceEq, if_pos, if_false, mul_one, mul_zero, zero_add]
  linear_combination (2 * Real.pi * r) * Real.cos_sq_add_sin_sq (2 * Real.pi * t)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem scalarConjugate_wedge (H : Plane → ℝ) (x v w : Plane) :
    fderiv ℝ H x v * scalarConjugateForm D H x w -
      fderiv ℝ H x w * scalarConjugateForm D H x v =
      (v 0 * w 1 - v 1 * w 0) * g.pullbackVolumeDensity id x *
        g.inner x (D.gradient H x) (D.gradient H x) := by
  rw [scalar_gradient_energy_coordinates, M60.plane_form_apply (fderiv ℝ H x) v,
    M60.plane_form_apply (fderiv ℝ H x) w]
  simp only [scalarConjugateForm, M60.rotatedFlux, scalarMetricFlux,
    add_apply, smul_apply, smul_eq_mul, EuclideanSpace.coe_proj]
  ring







theorem scalarCoverJacobian_eq_metric_energy {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    {z : Cover} (hz : z ∈ scalarCoverStrip) :
    scalarCoverJacobian D H z =
      (2 * Real.pi * z.1) * g.pullbackVolumeDensity id (scalarCoverMap z) *
        g.inner (scalarCoverMap z) (D.gradient H (scalarCoverMap z))
          (D.gradient H (scalarCoverMap z)) := by
  have hHd := (contMDiffAt_iff_contDiffAt.mp
    (hHs.contMDiffAt (scalarAnnulus_isOpen.mem_nhds (scalarCoverMap_mem hz)))).differentiableAt
      (by simp)
  rw [scalarCoverJacobian, fderiv_comp z hHd
    (scalarCoverMap_smooth.differentiable (by simp) z)]
  simp only [scalarCoverForm, ContinuousLinearMap.comp_apply]
  rw [scalarConjugate_wedge]
  rw [scalarCoverMap_column_determinant z.1 z.2]






theorem scalarCoverJacobian_nonneg {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    {z : Cover} (hz : z ∈ scalarCoverStrip) : 0 ≤ scalarCoverJacobian D H z := by
  rw [scalarCoverJacobian_eq_metric_energy D hHs hz]
  have hr : 0 < z.1 := lt_trans zero_lt_one hz.1
  have hrho : 0 < g.pullbackVolumeDensity id (scalarCoverMap z) :=
    (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
      (by simpa using Function.injective_id)).2
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hr.le)
    hrho.le) (scalarGradient_energy_nonneg D H _)







theorem scalarCoverWeightedFlux_mono {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    {r s : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) (hs : s ∈ Ioo (1 : ℝ) 2) (hrs : r ≤ s) :
    scalarCoverWeightedFlux D H r ≤ scalarCoverWeightedFlux D H s := by
  have hgreen := scalarCover_green_identity D hHs hlap hr hs hrs
  have hnon : 0 ≤ ∫ z in Icc (r, (0 : ℝ)) (s, 1), scalarCoverJacobian D H z := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact scalarCoverJacobian_nonneg D hHs ⟨hr.1.trans_le hz.1.1, hz.2.1.trans_lt hs.2⟩
  linarith

end PoincareConjecture.M64Uniformization
