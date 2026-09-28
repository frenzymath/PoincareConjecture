import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiCoordinates
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff Interval

namespace Complex




def beltramiRadialPrimitive (A : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, A (t • z) z

private def radialDerivative (A : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  A (t • z) + t • fderiv ℝ A (t • z) z

private theorem continuous_radialDerivative (A : ℂ → ℂ →L[ℝ] ℂ)
    (hA : ContDiff ℝ ∞ A) : Continuous (fun p : ℂ × ℝ => radialDerivative A p.1 p.2) := by
  have ht : Continuous (fun p : ℂ × ℝ => p.2 • p.1) := continuous_snd.smul continuous_fst
  exact (hA.continuous.comp ht).add (continuous_snd.smul
    (((hA.continuous_fderiv (by simp)).comp ht).clm_apply continuous_fst))

private theorem hasFDerivAt_radialIntegrand (A : ℂ → ℂ →L[ℝ] ℂ)
    (hA : ContDiff ℝ ∞ A)
    (hclosed : ∀ x u v, fderiv ℝ A x u v = fderiv ℝ A x v u) (z : ℂ) (t : ℝ) :
    HasFDerivAt (fun y => A (t • y) y) (radialDerivative A z t) z := by
  have hcomp := ((hA.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
    ((hasFDerivAt_id z).const_smul t)
  have hd := hcomp.clm_apply (hasFDerivAt_id z)
  convert! hd using 1
  ext v
  simp only [radialDerivative, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, map_smul,
    Function.comp_apply, Pi.smul_apply, id_eq]
  rw [hclosed (t • z) z v]

private theorem hasDerivAt_radialBoundaryTerm (A : ℂ → ℂ →L[ℝ] ℂ)
    (hA : ContDiff ℝ ∞ A) (z v : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s • A (s • z) v) (radialDerivative A z t v) t := by
  have hline : HasDerivAt (fun s : ℝ => s • z) z t := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id t).smul_const z
  have hcomp := ((hA.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt
    t hline
  have heval := hcomp.clm_apply (hasDerivAt_const t v)
  convert! (hasDerivAt_id t).smul heval using 1
  simp only [radialDerivative, add_apply, smul_apply, map_zero, add_zero, one_smul,
    Function.comp_apply, id_eq]
  exact _root_.add_comm _ _





theorem hasFDerivAt_beltramiRadialPrimitive (A : ℂ → ℂ →L[ℝ] ℂ)
    (hA : ContDiff ℝ ∞ A)
    (hclosed : ∀ x u v, fderiv ℝ A x u v = fderiv ℝ A x v u) (z : ℂ) :
    HasFDerivAt (beltramiRadialPrimitive A) (A z) z := by
  have hD := continuous_radialDerivative A hA
  have hDz : Continuous (radialDerivative A z) :=
    hD.comp (continuous_const.prodMk continuous_id)
  have hInt (x : ℂ) : Continuous (fun t : ℝ => A (t • x) x) :=
    (hA.continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod (isCompact_Icc (a := (0 : ℝ))
    (b := 1))).exists_bound_of_continuousOn hD.continuousOn
  have hderiv : HasFDerivAt (beltramiRadialPrimitive A)
      (∫ t in (0 : ℝ)..1, radialDerivative A z t) z := by
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := radialDerivative A) (bound := fun _ => C)
      (closedBall_mem_nhds z zero_lt_one)
    · exact Eventually.of_forall (fun x => (hInt x).aestronglyMeasurable)
    · exact (hInt z).intervalIntegrable _ _
    · exact hDz.aestronglyMeasurable
    · filter_upwards with t ht x hx
      apply hC (x, t)
      simp only [Set.mem_prod] at ⊢
      refine ⟨hx, ?_⟩
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨ht'.1.le, ht'.2⟩
    · exact intervalIntegrable_const
    · filter_upwards with t _ x _
      exact hasFDerivAt_radialIntegrand A hA hclosed x t
  have heq : (∫ t in (0 : ℝ)..1, radialDerivative A z t) = A z := by
    ext v
    rw [ContinuousLinearMap.intervalIntegral_apply (hDz.intervalIntegrable _ _)]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_radialBoundaryTerm A hA z v t)
      ((hDz.clm_apply continuous_const).intervalIntegrable (0 : ℝ) 1)
    simpa only [one_smul, zero_smul, sub_zero] using hFTC
  exact heq ▸ hderiv




theorem contDiff_beltramiRadialPrimitive (A : ℂ → ℂ →L[ℝ] ℂ)
    (hA : ContDiff ℝ ∞ A)
    (hclosed : ∀ x u v, fderiv ℝ A x u v = fderiv ℝ A x v u) :
    ContDiff ℝ ∞ (beltramiRadialPrimitive A) := by
  have hderiv := hasFDerivAt_beltramiRadialPrimitive A hA hclosed
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨fun z => (hderiv z).differentiableAt, ?_⟩
  have heq : fderiv ℝ (beltramiRadialPrimitive A) = A := funext (fun z => (hderiv z).fderiv)
  rw [heq]
  exact hA

end Complex
