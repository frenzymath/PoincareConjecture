import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.LocalInverse
import Mathlib.Analysis.Calculus.FDeriv.Symmetric



noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem hasDerivAt_variation
    {q : ℝ × E → E} {u : E → E} {t : ℝ} {v : E}
    (hq : ContDiffAt ℝ ∞ q (t, v))
    (hu : ∀ᶠ y in 𝓝 v, HasDerivAt (fun s => q (s, y)) (u y) t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => q (s, y)) v w)
      (fderiv ℝ u v w) t := by
  have hd := (hq.fderiv_right (m := 1)
    (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hn : ∀ᶠ p in 𝓝 (t, v), DifferentiableAt ℝ q p :=
    ((hq.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually
      (by decide)).mono fun p hp => hp.differentiableAt one_ne_zero
  have hs := hd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t v))
  have hl := hs.clm_apply (hasDerivAt_const t (0, w))
  simp only [ContinuousLinearMap.map_zero, add_zero] at hl
  have he : (fun s => fderiv ℝ (fun y => q (s, y)) v w) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ q (s, v) (0, w)) := by
    have ht : Tendsto (fun s : ℝ => (s, v)) (𝓝 t) (𝓝 (t, v)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually hn] with s hs
    have h := hs.hasFDerivAt.comp v
      ((hasFDerivAt_const (c := s) v).prodMk (hasFDerivAt_id v))
    simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] E => A w) h.fderiv
  have hspace := hd.hasFDerivAt.comp v
    ((hasFDerivAt_const (c := t) v).prodMk (hasFDerivAt_id v))
  have hr := hspace.clm_apply (hasFDerivAt_const (c := (1, (0 : E))) v)
  have he' : u =ᶠ[𝓝 v] (fun y => fderiv ℝ q (t, y) (1, 0)) := by
    have hv : Tendsto (fun y : E => (t, y)) (𝓝 v) (𝓝 (t, v)) :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hv.eventually hn, hu] with y hy huy
    have h := hy.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact huy.unique h
  have hr' := congrArg (fun A : E →L[ℝ] E => A w)
    (hr.congr_of_eventuallyEq he').fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.map_zero, zero_add,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] at hr'
  have hsym := hq.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    (1, 0) (0, w)
  apply (hl.congr_of_eventuallyEq he).congr_deriv
  simpa only [Function.comp_def] using hsym.trans hr'.symm


theorem fderiv_metric_symm
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = B y b a) (u a b : E) :
    fderiv ℝ B x u a b = fderiv ℝ B x u b a := by
  have ha := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).clm_apply
    (hasFDerivAt_const b x)
  have hb := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const b x)).clm_apply
    (hasFDerivAt_const a x)
  have he : (fun y => B y a b) =ᶠ[𝓝 x] (fun y => B y b a) :=
    hsymm.mono fun y hy => hy a b
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (ha.unique (hb.congr_of_eventuallyEq he))
  simpa using h


theorem hasDerivAt_geodesic_pairing
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q u J : ℝ → E} {K : E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (q t)) (hinv : (B (q t)).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 (q t), ∀ a b, B y a b = B y b a)
    (hq : HasDerivAt q (u t) t)
    (hu : HasDerivAt u (-coordinateChristoffel B (q t) (u t) (u t)) t)
    (hJ : HasDerivAt J K t) :
    HasDerivAt (fun s => B (q s) (u s) (J s))
      ((2⁻¹ : ℝ) * (fderiv ℝ B (q t) (J t) (u t) (u t) +
        B (q t) K (u t) + B (q t) (u t) K)) t := by
  have h := ((hB.hasFDerivAt.comp_hasDerivAt t hq).clm_apply hu).clm_apply hJ
  have hG := congrArg (fun L : E →L[ℝ] ℝ => L (J t))
    (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B (q t)) (u t) (u t)))
  change B (q t) (coordinateChristoffel B (q t) (u t) (u t)) (J t) = _ at hG
  simp only [metricKoszulCovector, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul] at hG
  rw [fderiv_metric_symm hB hsymm (u t) (J t) (u t)] at hG
  convert! h using 1
  simp only [Function.comp_apply, add_apply, map_neg, neg_apply]
  rw [hG, (hsymm.self_of_nhds) K (u t)]
  ring

end PoincareConjecture.CoordinateExponential
