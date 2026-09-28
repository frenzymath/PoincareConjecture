import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLipschitzDerivativeApproximation
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingBlend














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution NNReal

namespace PoincareConjecture.M64Uniformization

open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)





theorem scalarCutoffBlend_fderiv_apply {rho : Plane → ℝ} {u v : Plane → E}
    {x : Plane} (hrho : DifferentiableAt ℝ rho x)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (e : Plane) :
    fderiv ℝ (M40.cutoffBlend rho u v) x e = fderiv ℝ u x e +
      (fderiv ℝ rho x e) • (v x - u x) +
      rho x • (fderiv ℝ v x e - fderiv ℝ u x e) := by
  have heq : M40.cutoffBlend rho u v = fun y => u y + rho y • (v y - u y) := by
    funext y
    dsimp [M40.cutoffBlend]
    module
  rw [heq]
  change fderiv ℝ (u + rho • (v - u)) x e = _
  rw [(hu.hasFDerivAt.add (hrho.hasFDerivAt.smul
    (hv.hasFDerivAt.sub hu.hasFDerivAt))).fderiv]
  simp only [add_apply, sub_apply, smul_apply, smulRight_apply, Pi.sub_apply]
  module





theorem scalarMollifiedCutoff_lipschitz
    {u : Plane → E} {L A : ℝ≥0} (hu : LipschitzWith L u)
    {rho : Plane → ℝ} (hrho : LipschitzWith A rho) (hrange : ∀ x, rho x ∈ Icc 0 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    LipschitzWith (L + A * L)
      (M40.cutoffBlend rho u (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u)) := by
  apply lipschitzOnWith_univ.mp
  apply M40.cutoffBlend_lipschitzOn hrho.lipschitzOnWith
    (fun x _ => hrange x) hu.lipschitzOnWith
    (scalarVector_normed_convolution_lipschitz hu (mollifierBumpEps hr)).lipschitzOnWith
  intro x _
  exact (scalarVector_mollifier_error hu hr x).trans
    (mul_le_of_le_one_right L.coe_nonneg hr1)




theorem scalarMollifiedCutoff_uniform
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {rho : Plane → ℝ} (hrange : ∀ x, rho x ∈ Icc 0 1)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hz : Tendsto r atTop (𝓝 0)) :
    TendstoUniformly (fun j => M40.cutoffBlend rho u
      (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u)) u atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro eps heps
  have hbound : Tendsto (fun j => (L : ℝ) * r j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hz.const_mul (L : ℝ)
  filter_upwards [hbound.eventually (gt_mem_nhds heps)] with j hj x
  rw [dist_comm]
  exact (M40.cutoffBlend_dist_le (hrange x) (scalarVector_mollifier_error hu (hr j) x)).trans_lt hj





theorem scalarMollifiedCutoff_columns_tendsto_ae
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {rho : Plane → ℝ} (hrho : ContDiff ℝ ∞ rho)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hz : Tendsto r atTop (𝓝 0)) :
    ∀ᵐ x ∂volume, ∀ i : Fin 2,
      Tendsto (fun j => fderiv ℝ (M40.cutoffBlend rho u
        (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u)) x (EuclideanSpace.single i 1))
        atTop (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1))) := by
  filter_upwards [hu.ae_differentiableAt (μ := volume),
    scalarLipschitz_mollifier_columns_tendsto_ae hu hr hz] with x hx hcol
  intro i
  simp_rw [scalarCutoffBlend_fderiv_apply (hrho.differentiable (by simp) x) hx
    ((scalarVector_mollifier_smooth hu _).differentiable (by simp) x)]
  have hv := (scalarVector_mollifier_uniform hu hr hz).tendsto_at x
  have hterm0 := (hv.sub_const (u x)).const_smul (fderiv ℝ rho x (EuclideanSpace.single i 1))
  have hterm1 := ((hcol i).sub_const
    (fderiv ℝ u x (EuclideanSpace.single i 1))).const_smul (rho x)
  simpa only [sub_self, smul_zero, add_zero] using
    (tendsto_const_nhds.add hterm0).add hterm1




theorem scalarMollifiedCutoff_preserves_C1
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {rho : Plane → ℝ} (hrho : ContDiff ℝ ∞ rho)
    {r : ℝ} (hr : 0 < r) {x : Plane} (hx : ContDiffAt ℝ 1 u x) :
    ContDiffAt ℝ 1 (M40.cutoffBlend rho u
      (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u)) x := by
  exact ((hrho.contDiffAt.of_le (by simp)).smul
    ((scalarVector_mollifier_smooth hu hr).contDiffAt.of_le (by simp))).add
    ((contDiffAt_const.sub (hrho.contDiffAt.of_le (by simp))).smul hx)




theorem scalarMollifiedCutoff_smooth_on_plateau
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {rho : Plane → ℝ} {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : rho =ᶠ[𝓝 x] 1) :
    ContDiffAt ℝ ∞ (M40.cutoffBlend rho u
      (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u)) x := by
  apply (scalarVector_mollifier_smooth hu hr).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hx] with y hy
  exact M40.cutoffBlend_eq_right hy





theorem scalarMollifiedCutoff_eq_outside
    (u : Plane → E) (rho : Plane → ℝ) {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∉ tsupport rho) :
    M40.cutoffBlend rho u (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) =ᶠ[𝓝 x] u := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  exact M40.cutoffBlend_eq_left hy

end PoincareConjecture.M64Uniformization
