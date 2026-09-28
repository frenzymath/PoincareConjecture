import PoincareConjecture.Proofs.M35.RadialGauge.RadiusInverse
import Mathlib.Analysis.Calculus.ImplicitContDiff











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge



noncomputable def mapRadiusInverse (w : ℝ → ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  Function.invFun (mapRadius (w t))



theorem mapRadius_inverse_properties {w : ℝ → ℝ → ℝ} {t : ℝ}
    (hw : ContDiff ℝ ∞ (w t))
    (hv : ∀ r, (1 + |r|) * |w t r| ≤ 1 / 8)
    (hd : ∀ r, (1 + |r|) * |deriv (w t) r| ≤ 1 / 8) :
    ContDiff ℝ ∞ (mapRadiusInverse w t) ∧
    Function.LeftInverse (mapRadiusInverse w t) (mapRadius (w t)) ∧
    Function.RightInverse (mapRadiusInverse w t) (mapRadius (w t)) ∧
    Function.Injective (mapRadius (w t)) := by
  obtain ⟨q, hqs, hql, hqr⟩ := exists_mapRadius_smooth_inverse hw hv hd
  have hinj : Function.Injective (mapRadius (w t)) :=
    Function.LeftInverse.injective hql
  have hsurj : Function.Surjective (mapRadius (w t)) :=
    Function.RightInverse.surjective hqr
  have hl := Function.leftInverse_invFun hinj
  have hr := Function.rightInverse_invFun hsurj
  have heq : mapRadiusInverse w t = q := by
    funext r
    apply hinj
    exact (hr r).trans (hqr r).symm
  refine ⟨?_, hl, hr, hinj⟩
  rw [heq]
  exact hqs



theorem mapRadiusInverse_contDiffAt
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (w t))
    (hv : ∀ t ∈ J, ∀ r, (1 + |r|) * |w t r| ≤ 1 / 8)
    (hd : ∀ t ∈ J, ∀ r, (1 + |r|) * |deriv (w t) r| ≤ 1 / 8)
    {p : ℝ × ℝ} (hp : p.1 ∈ J) :
    ContDiffAt ℝ 1 (Function.uncurry (mapRadiusInverse w)) p := by
  let r := mapRadiusInverse w p.1 p.2
  let H (z : (ℝ × ℝ) × ℝ) := mapRadius (w z.1.1) z.2 - z.1.2
  have hρ : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => mapRadius (w z.1) z.2)
      (J ×ˢ univ) := contDiffOn_snd.mul hc.exp
  have hρAt : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => mapRadius (w z.1) z.2) (p.1, r) :=
    hρ.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hp, mem_univ r⟩)
  have hH : ContDiffAt ℝ 1 H (p, r) :=
    (hρAt.comp (p, r)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hprop := mapRadius_inverse_properties (hs p.1 hp) (hv p.1 hp) (hd p.1 hp)
  have hvalue : H (p, r) = 0 := by
    dsimp only [H, r]
    rw [hprop.2.2.1 p.2, sub_self]
  let d := deriv (mapRadius (w p.1)) r
  have hdpos : 0 < d := by
    have h := mapRadius_deriv_sub_one_bound (hs p.1 hp) r (hv p.1 hp r) (hd p.1 hp r)
    dsimp only [d]
    linarith only [(abs_le.mp h).1]
  have hpart : fderiv ℝ H (p, r) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ d := by
    have hfirst := (hH.differentiableAt (by norm_num)).hasFDerivAt.comp r
      (hasFDerivAt_prodMk_right p r)
    have hsecond : HasDerivAt (fun q => H (p, q)) d r :=
      (((contDiff_id.mul (hs p.1 hp).exp).differentiable (by simp) r).hasDerivAt).sub_const p.2
    exact hfirst.unique hsecond.hasFDerivAt
  have hinv : (fderiv ℝ H (p, r) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    rw [hpart]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
    · apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp [hdpos.ne']
    · apply ContinuousLinearMap.ext
      intro a
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp [hdpos.ne']
  let q := hH.implicitFunction (by norm_num) hinv
  have hq : ContDiffAt ℝ 1 q p := hH.contDiffAt_implicitFunction (by norm_num) hinv
  have heq : ∀ᶠ z in 𝓝 p, H (z, q z) = 0 := by
    simpa only [hvalue] using hH.eventually_apply_implicitFunction (by norm_num) hinv
  have htime : ∀ᶠ z : ℝ × ℝ in 𝓝 p, z.1 ∈ J :=
    continuous_fst.continuousAt.eventually (hJ.mem_nhds hp)
  apply hq.congr_of_eventuallyEq
  filter_upwards [heq, htime] with z hz hzt
  have hprops := mapRadius_inverse_properties (hs z.1 hzt) (hv z.1 hzt) (hd z.1 hzt)
  apply hprops.2.2.2
  dsimp only [Function.uncurry]
  rw [hprops.2.2.1 z.2]
  exact (sub_eq_zero.mp hz).symm

end PoincareConjecture.M35.RadialGauge
