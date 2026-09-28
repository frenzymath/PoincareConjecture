import PoincareConjecture.Proofs.M10.ProductDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul









set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option backward.isDefEq.respectTransparency false in

theorem endpoint_gram_hasDerivAt
    {E : X × ℝ → Y} {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {z : X × ℝ}
    (hE : ContDiffAt ℝ 2 E z) (hB : DifferentiableAt ℝ B (E z, z.2)) (h k : X) :
    HasDerivAt
      (fun t ↦ B (E (z.1, t), t)
        (fderiv ℝ E (z.1, t) (h, 0)) (fderiv ℝ E (z.1, t) (k, 0)))
      (fderiv ℝ B (E z, z.2) (fderiv ℝ E z (0, 1), 1)
          (fderiv ℝ E z (h, 0)) (fderiv ℝ E z (k, 0)) +
        B (E z, z.2) (fderiv ℝ (fderiv ℝ E) z (0, 1) (h, 0))
          (fderiv ℝ E z (k, 0)) +
        B (E z, z.2) (fderiv ℝ E z (h, 0))
          (fderiv ℝ (fderiv ℝ E) z (0, 1) (k, 0))) z.2 := by
  have hDE := (hE.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD (v : X × ℝ) : HasDerivAt
      (fun t ↦ fderiv ℝ E (z.1, t) v)
      (fderiv ℝ (fderiv ℝ E) z (0, 1) v) z.2 := by
    simpa only [map_zero, add_zero] using
      (hasDerivAt_time_slice hDE).clm_apply (hasDerivAt_const z.2 v)
  have hBt : HasDerivAt (fun t ↦ B (E (z.1, t), t))
      (fderiv ℝ B (E z, z.2) (fderiv ℝ E z (0, 1), 1)) z.2 := by
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Y × ℝ)
      (E := Y →L[ℝ] Y →L[ℝ] ℝ) (l := B)
      (f := fun t : ℝ ↦ (E (z.1, t), t)) z.2 hB.hasFDerivAt
      ((hasDerivAt_time_slice (hE.differentiableAt two_ne_zero)).prodMk (hasDerivAt_id z.2))
  simpa only [add_apply] using (hBt.clm_apply (hD (h, 0))).clm_apply
    (hD (k, 0))

set_option backward.isDefEq.respectTransparency false in

theorem terminal_pairing_second_derivative
    {E : X × ℝ → Y} {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {l : Y → ℝ}
    {z : X × ℝ} (hE : ContDiffAt ℝ 2 E z)
    (hB : DifferentiableAt ℝ B (E z, z.2)) (hl : ContDiffAt ℝ 2 l (E z))
    (h : X) (v : Y)
    (hpair : ∀ᶠ V in 𝓝 z.1,
      fderiv ℝ l (E (V, z.2)) v =
        B (E (V, z.2), z.2) (fderiv ℝ E (V, z.2) (0, 1)) v) :
    fderiv ℝ (fderiv ℝ l) (E z) (fderiv ℝ E z (h, 0)) v =
      fderiv ℝ B (E z, z.2) (fderiv ℝ E z (h, 0), 0)
          (fderiv ℝ E z (0, 1)) v +
        B (E z, z.2) (fderiv ℝ (fderiv ℝ E) z (0, 1) (h, 0)) v := by
  let i : X →L[ℝ] X × ℝ := (ContinuousLinearMap.id ℝ X).prod 0
  have hi : HasFDerivAt (fun V : X ↦ (V, z.2)) i z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hEs := (hE.differentiableAt two_ne_zero).hasFDerivAt.comp z.1 hi
  have hDE := (hE.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDs := hDE.hasFDerivAt.comp z.1 hi
  have hlD := (hl.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hls := hlD.hasFDerivAt.comp z.1 hEs
  have hBs : HasFDerivAt (fun V ↦ B (E (V, z.2), z.2))
      ((fderiv ℝ B (E z, z.2)).comp (((fderiv ℝ E z).comp i).prod 0)) z.1 := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := X) (F := Y × ℝ)
      (G := Y →L[ℝ] Y →L[ℝ] ℝ) (g := B)
      (f := fun V : X ↦ (E (V, z.2), z.2)) z.1 hB.hasFDerivAt
      (hEs.prodMk (hasFDerivAt_const z.2 z.1))
  have hleft := hls.clm_apply (hasFDerivAt_const v z.1)
  have hright := (hBs.clm_apply (hDs.clm_apply (hasFDerivAt_const (0, 1) z.1))).clm_apply
    (hasFDerivAt_const v z.1)
  have hEq := congrArg (fun D : X →L[ℝ] ℝ ↦ D h)
    ((hleft.congr_of_eventuallyEq (Filter.EventuallyEq.symm hpair)).unique hright)
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    map_zero, zero_add, Function.comp_def, Prod.eta, i] at hEq
  rw [← (hE.isSymmSndFDerivAt (by simp)).eq (0, 1) (h, 0)] at hEq
  simpa only [add_comm] using hEq

end PoincareConjecture.M10
