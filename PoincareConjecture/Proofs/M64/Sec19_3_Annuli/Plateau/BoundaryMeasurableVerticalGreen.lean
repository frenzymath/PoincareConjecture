import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnBoundary
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64Annulus_measurable_vertical_green
    {q : ℝ → ℝ} (hq : MemLp q 2 (volume.restrict I))
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, fderiv ℝ phi p e1 * q (p 0)) =
      ∫ x in I, phi (annulusPoint x 1) * q x -
        phi (annulusPoint x 0) * q x := by
  have hqP : MemLp (fun p : LoopPlane => q (p 0)) 2 (volume.restrict S) :=
    hq.comp_measurePreserving m64Annulus_angular_projection_measurePreserving
  have hd : Continuous (fun p : LoopPlane => fderiv ℝ phi p e1) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi : IntegrableOn (fun p => fderiv ℝ phi p e1 * q (p 0)) S :=
    (m64Annulus_continuous_memLp_two hd).integrable_mul hqP
  rw [m64AnnulusInteriorIntegral_eq_iterated_integrable _ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hd' : Continuous (fun s : ℝ => fderiv ℝ phi (annulusPoint x s) e1) := by
    apply hd.comp
    unfold annulusPoint
    fun_prop
  have hder (s : ℝ) : HasDerivAt (fun t => phi (annulusPoint x t))
      (fderiv ℝ phi (annulusPoint x s) e1) s :=
    (hphi.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s
      (m64AnnulusPoint_vertical_hasDerivAt x s)
  change (∫ s in Icc (0 : ℝ) 1,
    fderiv ℝ phi (annulusPoint x s) e1 * q x) = _
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
      (hd'.intervalIntegrable 0 1)]
  ring

end PoincareConjecture
