import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Circle.Normal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)

def intervalFamilyVelocity (f : Real × Real -> E2) (z : Real × Real) : E2 :=
  deriv (fun s => f (z.1, s)) z.2

theorem contDiff_intervalFamilyVelocity {f : Real × Real -> E2}
    (hf : ContDiff Real ∞ f) : ContDiff Real ∞ (intervalFamilyVelocity f) := by
  have hA : ContDiff Real ∞ (fun z : Real × Real =>
      fderiv Real (fun s => f (z.1, s)) z.2) :=
    (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv contDiff_snd (by simp)
  exact hA.clm_apply contDiff_const

def intervalNormalThickening (f : Real × Real -> E2) (z : Real × E2) : E2 :=
  f (z.1, z.2 0) + (z.2 1) • circleQuarterTurn (intervalFamilyVelocity f (z.1, z.2 0))

theorem contDiff_intervalNormalThickening {f : Real × Real -> E2}
    (hf : ContDiff Real ∞ f) : ContDiff Real ∞ (intervalNormalThickening f) := by
  have hq : ContDiff Real ∞ (fun z : Real × E2 => (z.1, z.2 0)) :=
    contDiff_fst.prodMk
      ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp contDiff_snd)
  exact (hf.comp hq).add
    (((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd).smul
    (circleQuarterTurn.contDiff.comp ((contDiff_intervalFamilyVelocity hf).comp hq)))

theorem intervalNormalThickening_zero {f : Real × Real -> E2}
    (t : Real) (x : E2) (hx : x 1 = 0) : intervalNormalThickening f (t, x) = f (t, x 0) := by
  simp [intervalNormalThickening, hx]

theorem fderiv_intervalNormalThickening_zero {f : Real × Real -> E2}
    (hf : ContDiff Real ∞ f) (t : Real) (x : E2) (hx : x 1 = 0) (v : E2) :
    fderiv Real (fun y => intervalNormalThickening f (t, y)) x v =
      (v 0) • intervalFamilyVelocity f (t, x 0) +
        (v 1) • circleQuarterTurn (intervalFamilyVelocity f (t, x 0)) := by
  have hslice : ContDiff Real ∞ (fun s : Real => f (t, s)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hN : ContDiff Real ∞ (fun y : E2 =>
      circleQuarterTurn (intervalFamilyVelocity f (t, y 0))) :=
    circleQuarterTurn.contDiff.comp ((contDiff_intervalFamilyVelocity hf).comp
      (contDiff_const.prodMk (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff))
  have hd := ((hslice.differentiable (by simp) (x 0)).hasFDerivAt.comp x
    (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).hasFDerivAt).add
      ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).hasFDerivAt.smul
        ((hN.differentiable (by simp) x).hasFDerivAt))
  have heq := congrArg (fun L : E2 →L[Real] E2 => L v) hd.fderiv
  simpa only [intervalNormalThickening, intervalFamilyVelocity, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, EuclideanSpace.coe_proj, hx, zero_smul,
    zero_add, ContinuousLinearMap.comp_apply, Pi.add_def, Pi.smul_apply', Function.comp_def,
    fderiv_eq_smul_deriv] using heq

theorem bijective_fderiv_intervalNormalThickening_zero {f : Real × Real -> E2}
    (hf : ContDiff Real ∞ f) (t : Real) (x : E2) (hx : x 1 = 0)
    (hvel : deriv (fun s => f (t, s)) (x 0) ≠ 0) :
    Function.Bijective (fderiv Real (fun y => intervalNormalThickening f (t, y)) x) := by
  have hn : inner Real (intervalFamilyVelocity f (t, x 0))
      (intervalFamilyVelocity f (t, x 0)) ≠ 0 := by
    simpa only [ne_eq, inner_self_eq_zero, intervalFamilyVelocity] using hvel
  have hnn : inner Real (circleQuarterTurn (intervalFamilyVelocity f (t, x 0)))
      (circleQuarterTurn (intervalFamilyVelocity f (t, x 0))) ≠ 0 := by
    simpa only [circleQuarterTurn.inner_map_map] using hn
  have hi : Function.Injective (fderiv Real (fun y => intervalNormalThickening f (t, y)) x) := by
    intro u v huv
    rw [fderiv_intervalNormalThickening_zero hf t x hx u,
      fderiv_intervalNormalThickening_zero hf t x hx v] at huv
    have hfirst := congrArg (inner Real (intervalFamilyVelocity f (t, x 0))) huv
    simp only [inner_add_right, inner_smul_right, inner_self_circleQuarterTurn,
      mul_zero, add_zero] at hfirst
    have hu0 : u 0 = v 0 := mul_right_cancel₀ hn hfirst
    have hsecond := congrArg
      (inner Real (circleQuarterTurn (intervalFamilyVelocity f (t, x 0)))) huv
    simp only [inner_add_right, inner_smul_right, inner_circleQuarterTurn_self,
      mul_zero, zero_add] at hsecond
    have hu1 : u 1 = v 1 := mul_right_cancel₀ hnn hsecond
    ext i
    fin_cases i
    · exact hu0
    · exact hu1
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

end Poincare.Manifold.Schoenflies
