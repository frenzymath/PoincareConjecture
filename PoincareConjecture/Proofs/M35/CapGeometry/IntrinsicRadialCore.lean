import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialDistance
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.InnerProductSpace.Calculus











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology Pointwise

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (P : M35StandardCapPredecessors)

include hrotation hcomplete P



theorem closure_ball_zero_eq_radial_closedBall {s : ℝ} (hs : 0 < s) :
    closure (g.ball 0 s) =
      closedBall 0 ((radialArclengthOrderIso g hrotation hcomplete).symm s) := by
  have hr : 0 < (radialArclengthOrderIso g hrotation hcomplete).symm s := by
    simpa only [radialArclengthOrderIso_symm_zero] using
      (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono hs
  rw [ball_zero_eq_radial_ball g hrotation hcomplete P, closure_ball 0 hr.ne']



theorem radial_metric_ball_closed_core_witness {s : ℝ} (hs : 0 < s) :
    ∃ f : StandardCapSpace → StandardCapSpace,
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (closedBall 0 1) ∧
      InjOn f (closedBall 0 1) ∧
      (∀ p ∈ closedBall (0 : StandardCapSpace) 1,
        Function.Injective (mfderiv (𝓡 3) (𝓡 3) f p)) ∧
      f '' closedBall 0 1 = closure (g.ball 0 s) ∧
      f '' sphere 0 1 = frontier (closure (g.ball 0 s)) := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hr : 0 < r := by
    simpa only [radialArclengthOrderIso_symm_zero] using
      (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono hs
  let f : StandardCapSpace → StandardCapSpace := fun x => r • x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (contDiff_id.const_smul r).contMDiff
  have hinj : Function.Injective f := smul_right_injective StandardCapSpace hr.ne'
  refine ⟨f, hf.contMDiffOn, hinj.injOn, ?_, ?_, ?_⟩
  · intro p _hp
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ (fun x : StandardCapSpace => r • x) p)
    have hd : HasFDerivAt (fun x : StandardCapSpace => r • x)
        (r • ContinuousLinearMap.id ℝ StandardCapSpace) p :=
      (hasFDerivAt_id p).const_smul r
    rw [hd.fderiv]
    change Function.Injective (fun v : StandardCapSpace => r • v)
    exact hinj
  · rw [closure_ball_zero_eq_radial_closedBall g hrotation hcomplete P hs]
    change r • closedBall (0 : StandardCapSpace) 1 = closedBall 0 r
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one] using
      smul_closedBall' hr.ne' (0 : StandardCapSpace) 1
  · rw [closure_ball_zero_eq_radial_closedBall g hrotation hcomplete P hs,
      frontier_closedBall 0 hr.ne']
    change r • sphere (0 : StandardCapSpace) 1 = sphere 0 r
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one] using
      smul_sphere' hr.ne' (0 : StandardCapSpace) 1



theorem radial_metric_ball_carrier_witness {s : ℝ} (hs : 0 < s) :
    ∃ f h : StandardCapSpace → StandardCapSpace,
      range f = g.ball 0 s ∧ Function.LeftInverse h f ∧
      LeftInvOn f h (g.ball 0 s) ∧
      ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ h (g.ball 0 s) := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hr : 0 < r := by
    simpa only [radialArclengthOrderIso_symm_zero] using
      (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono hs
  let e := OpenPartialHomeomorph.univBall (0 : StandardCapSpace) r
  have hball : g.ball 0 s = ball (0 : StandardCapSpace) r :=
    ball_zero_eq_radial_ball g hrotation hcomplete P s
  refine ⟨e, e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hball]
    have he := e.image_source_eq_target
    simpa only [e, OpenPartialHomeomorph.univBall_source,
      OpenPartialHomeomorph.univBall_target _ hr, image_univ] using he
  · intro x
    exact e.left_inv (by simp [e])
  · intro x hx
    apply e.right_inv
    simpa only [e, OpenPartialHomeomorph.univBall_target _ hr, ← hball] using hx
  · exact OpenPartialHomeomorph.contDiff_univBall.contMDiff
  · rw [hball]
    exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn


theorem radial_metric_ball_core_compact {s : ℝ} (hs : 0 < s) :
    IsCompact (closure (g.ball 0 s)) := by
  rw [closure_ball_zero_eq_radial_closedBall g hrotation hcomplete P hs]
  exact isCompact_closedBall _ _

end PoincareConjecture.M35.Uniqueness
