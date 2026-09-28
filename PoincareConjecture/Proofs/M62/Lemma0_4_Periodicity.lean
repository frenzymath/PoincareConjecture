import PoincareConjecture.Proofs.M62.Cor0_3_RegularizedEvolution
import PoincareConjecture.Proofs.M09.VelocityChainRules
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem speed_periodic
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    Function.Periodic (curveSpeed F c t) curvePeriod := by
  intro x
  have hcurve : (fun y => c (y + curvePeriod) t) = (fun y => c y t) :=
    funext (hc.periodic t ht)
  have hshift : HasDerivAt (fun y : ℝ => y + curvePeriod) 1 x :=
    (hasDerivAt_id x).add_const curvePeriod
  have hvalue : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun y : ℝ => y + curvePeriod) x 1 = 1 := by
    rw [mfderiv_eq_fderiv, hshift.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ 1
  have hcomp := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
    (mfderiv_comp (f := fun y : ℝ => y + curvePeriod) (g := fun y => c y t) x
      ((hc.spatial_regular t ht (x + curvePeriod)).mdifferentiableAt (by norm_num))
      hshift.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c (y + curvePeriod) t) x 1 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t) (x + curvePeriod)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => y + curvePeriod) x 1) at hcomp
  rw [hvalue] at hcomp
  change (curveVelocity (fun y => c (y + curvePeriod) t) x :
    EuclideanSpace ℝ (Fin n)) = curveVelocity (fun y => c y t) (x + curvePeriod) at hcomp
  rw [hcurve] at hcomp
  change (F.metric t).tangentNorm (c (x + curvePeriod) t)
      (curveVelocity (fun y => c y t) (x + curvePeriod)) =
    (F.metric t).tangentNorm (c x t) (curveVelocity (fun y => c y t) x)
  rw [← hcomp, hc.periodic t ht x]



theorem curvatureSquared_periodic
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    Function.Periodic (m62CurvatureSquared F c t) curvePeriod := by
  intro x
  have heq : (fun s => c (x + curvePeriod) s) =ᶠ[𝓝 t] (fun s => c x s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hc.periodic s (Set.Ioo_subset_Icc_self hs) x
  have hvel := PoincareConjecture.Proofs.M09.curveVelocity_congr_of_eventuallyEq (n := n) heq
  rw [hc.equation t ht (x + curvePeriod), hc.equation t ht x] at hvel
  dsimp only [m62CurvatureSquared]
  rw [hvel, hc.periodic t (Set.Ioo_subset_Icc_self ht) x]



theorem integral_regularized_arcSecond_eq_zero
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {ε t : ℝ}
    (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) :
    (∫ x in (0 : ℝ)..curvePeriod,
      m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x *
        curveSpeed F c t x) = 0 := by
  let h := m62RegularizedCurvature F c ε t
  have hh : ContDiff ℝ ∞ h :=
    (regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hL : ContDiff ℝ ∞ (m62ArcDerivative F c t h) :=
    (hv.inv (fun y => (speed_pos F c hc (Set.Ioo_subset_Icc_self ht) y).ne')).mul
      (contDiff_infty_iff_deriv.mp hh).2
  have hp : Function.Periodic h curvePeriod := by
    intro y
    dsimp only [h, m62RegularizedCurvature]
    rw [curvatureSquared_periodic F c hc ht y]
  have hdp : Function.Periodic (deriv h) curvePeriod := by
    intro y
    rw [← deriv_comp_add_const]
    congr 1
    exact funext hp
  have hLp : Function.Periodic (m62ArcDerivative F c t h) curvePeriod := by
    intro y
    dsimp only [m62ArcDerivative]
    rw [speed_periodic F c hc (Set.Ioo_subset_Icc_self ht) y, hdp y]
  calc
    _ = ∫ x in (0 : ℝ)..curvePeriod, deriv (m62ArcDerivative F c t h) x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [m62ArcSecondDerivative, m62ArcDerivative]
      have hspeed := (speed_pos F c hc (Set.Ioo_subset_Icc_self ht) x).ne'
      field_simp
      rfl
    _ = m62ArcDerivative F c t h curvePeriod - m62ArcDerivative F c t h 0 :=
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => (hL.differentiable (by simp)) x)
        ((contDiff_infty_iff_deriv.mp hL).2.continuous.intervalIntegrable _ _)
    _ = 0 := by
      have he := hLp 0
      rw [zero_add] at he
      rw [he, sub_self]

end PoincareConjecture.M62
