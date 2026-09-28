import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace PoincareConjecture.M35.Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def quadraticJet (c : ℝ) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) : ℝ :=
  c + L (y - x) + (1 / 2 : ℝ) * B (y - x) (y - x)

theorem quadraticJet_contDiff (c : ℝ) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    ContDiff ℝ ∞ (quadraticJet c L B x) := by
  unfold quadraticJet
  exact (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))).add
    (contDiff_const.mul ((B.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
      (contDiff_id.sub contDiff_const)))

@[simp] theorem quadraticJet_self (c : ℝ) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : quadraticJet c L B x x = c := by
  simp [quadraticJet]

theorem quadraticJet_hasFDerivAt (c : ℝ) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ a b, B a b = B b a) (x y : E) :
    HasFDerivAt (quadraticJet c L B x) (L + B (y - x)) y := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
  have hlin := L.hasFDerivAt.comp y hsub
  have hquad := ((hasFDerivAt_const B y).clm_apply hsub).clm_apply hsub
  convert! (hlin.const_add c).add (hquad.const_mul (1 / 2 : ℝ)) using 1
  ext v
  simp only [ContinuousLinearMap.comp_id, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply, zero_apply, add_zero, id_eq]
  rw [hB v (y - x)]
  ring

theorem quadraticJet_fderiv (c : ℝ) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ a b, B a b = B b a) (x : E) :
    fderiv ℝ (quadraticJet c L B x) = fun y => L + B (y - x) :=
  funext (fun y => (quadraticJet_hasFDerivAt c L B hB x y).fderiv)

theorem quadraticJet_second_fderiv (c : ℝ) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ a b, B a b = B b a) (x y : E) :
    fderiv ℝ (fderiv ℝ (quadraticJet c L B x)) y = B := by
  rw [quadraticJet_fderiv c L B hB]
  have hd := (B.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)).const_add L
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using hd.fderiv

theorem quadraticJet_remainder_isLittleO {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    (fun y => f y - quadraticJet (f x) (fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) x) x y) =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
  let L := fderiv ℝ f x
  let B := fderiv ℝ (fderiv ℝ f) x
  let q := quadraticJet (f x) L B x
  have hB : ∀ a b, B a b = B b a := hf.isSymmSndFDerivAt (by simp)
  have hd : HasFDerivAt (fderiv ℝ f) B x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually (by norm_num))
  have hrem : (fun y => fderiv ℝ f y - (L + B (y - x))) =o[𝓝 x]
      (fun y => ‖y - x‖ ^ 1) := by
    simpa only [L, sub_add_eq_sub_sub, pow_one] using hd.isLittleO.norm_right
  have h := (convex_ball x r).isLittleO_pow_succ (n := 1)
    (Metric.mem_ball_self hr) (f := fun y => f y - q y)
    (f' := fun y => fderiv ℝ f y - (L + B (y - x)))
    (fun y hy => ((hball (Metric.mem_ball.mp hy)).differentiableAt (by norm_num)).hasFDerivAt.sub
      (quadraticJet_hasFDerivAt (f x) L B hB x y) |>.hasFDerivWithinAt)
    (hrem.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hr)] at h
  simpa only [q, quadraticJet_self, sub_self, sub_zero] using h

end PoincareConjecture.M35.Uniqueness
