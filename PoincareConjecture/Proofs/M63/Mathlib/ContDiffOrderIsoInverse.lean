import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M63

theorem contDiffAt_inverse_orderIso_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (phi : E → (ℝ ≃o ℝ)) {z : E} {y d : ℝ} {k : ℕ∞ω} (hk : k ≠ 0)
    (hphi : ContDiffAt ℝ k (fun p : E × ℝ => phi p.1 p.2) (z, (phi z).symm y))
    (hderiv : HasDerivAt (phi z) d ((phi z).symm y)) (hd : d ≠ 0) :
    ContDiffAt ℝ k (fun p : E × ℝ => (phi p.1).symm p.2) (z, y) := by
  let x := (phi z).symm y
  let H : (E × ℝ) × ℝ → ℝ := fun p => phi p.1.1 p.2 - p.1.2
  have hmap : ContDiffAt ℝ k (fun p : (E × ℝ) × ℝ => (p.1.1, p.2)) ((z, y), x) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have hH : ContDiffAt ℝ k H ((z, y), x) :=
    (hphi.comp (f := fun p : (E × ℝ) × ℝ => (p.1.1, p.2))
      (g := fun p : E × ℝ => phi p.1 p.2) ((z, y), x) hmap).sub contDiffAt_fst.snd
  have hprod : (0 : ℝ →L[ℝ] E × ℝ).prod (ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.inr ℝ (E × ℝ) ℝ := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hslice : HasFDerivAt (fun u => H ((z, y), u))
      ((fderiv ℝ H ((z, y), x)).comp (ContinuousLinearMap.inr ℝ (E × ℝ) ℝ)) x := by
    simpa only [Function.comp_def, hprod] using
      (hH.differentiableAt hk).hasFDerivAt.comp x
        ((hasFDerivAt_const (z, y) x).prodMk (hasFDerivAt_id x))
  have hactual : HasDerivAt (fun u => H ((z, y), u)) d x := hderiv.sub_const y
  have hpartial : (fderiv ℝ H ((z, y), x)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) ℝ) = d • ContinuousLinearMap.id ℝ ℝ := by
    rw [hslice.unique hactual.hasFDerivAt]
    apply ContinuousLinearMap.ext
    intro u
    change u * d = d * u
    exact mul_comm _ _
  have hinv : ((fderiv ℝ H ((z, y), x)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) ℝ)).IsInvertible := by
    rw [hpartial]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hd, one_smul]
    · apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ hd, one_smul]
  let q := hH.implicitFunction hk hinv
  have hzero : H ((z, y), x) = 0 := by
    simp only [H, x, OrderIso.apply_symm_apply, sub_self]
  have heq : (fun p : E × ℝ => (phi p.1).symm p.2) =ᶠ[𝓝 (z, y)] q := by
    have hlocal := hH.eventually_apply_implicitFunction hk hinv
    filter_upwards [hlocal] with p hp
    apply (phi p.1).injective
    rw [OrderIso.apply_symm_apply]
    have hroot : phi p.1 (q p) - p.2 = 0 := hp.trans hzero
    exact (sub_eq_zero.mp hroot).symm
  exact (hH.contDiffAt_implicitFunction hk hinv).congr_of_eventuallyEq heq

theorem hasDerivAt_time_inverse_orderIso_family
    (phi : ℝ → (ℝ ≃o ℝ)) {t y dx dt : ℝ}
    (hphi : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => phi p.1 p.2) (t, (phi t).symm y))
    (hx : HasDerivAt (phi t) dx ((phi t).symm y))
    (ht : HasDerivAt (fun s => phi s ((phi t).symm y)) dt t) (hdx : dx ≠ 0) :
    HasDerivAt (fun s => (phi s).symm y) (-dt / dx) t := by
  let psi : ℝ → ℝ := fun s => (phi s).symm y
  let x := psi t
  let w := deriv psi t
  have hinv := contDiffAt_inverse_orderIso_family phi (by norm_num) hphi hx hdx
  have hpsi : HasDerivAt psi w t :=
    ((hinv.comp (f := fun s : ℝ => (s, y))
      (g := fun p : ℝ × ℝ => (phi p.1).symm p.2) t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by norm_num)).hasDerivAt
  let G : ℝ × ℝ → ℝ := fun p => phi p.1 p.2
  let D := fderiv ℝ G (t, x)
  have hD : HasFDerivAt G D (t, x) := (hphi.differentiableAt (by norm_num)).hasFDerivAt
  have hDt : D (1, 0) = dt :=
    (hD.comp_hasDerivAt (f := fun s : ℝ => (s, x)) t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).unique ht
  have hDx : D (0, 1) = dx :=
    (hD.comp_hasDerivAt (f := fun u : ℝ => (t, u)) x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))).unique hx
  have hvalue : D (1, w) = dt + w * dx := by
    have hp : ((1 : ℝ), w) = (1, 0) + w • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hp, map_add, map_smul, hDt, hDx, smul_eq_mul]
  have hcomp : HasDerivAt (fun s => phi s (psi s)) (D (1, w)) t :=
    hD.comp_hasDerivAt (f := fun s => (s, psi s)) t
      ((hasDerivAt_id t).prodMk hpsi)
  have heq : (fun s => phi s (psi s)) = fun _ => y :=
    funext fun s => (phi s).apply_symm_apply y
  rw [heq] at hcomp
  have hzero : dt + w * dx = 0 := hvalue.symm.trans (hcomp.unique (hasDerivAt_const t y))
  apply hpsi.congr_deriv
  apply (eq_div_iff hdx).mpr
  linarith only [hzero]

end PoincareConjecture.M63
