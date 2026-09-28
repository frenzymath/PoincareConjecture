import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem reverse_inj {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hi : InjOn gamma (Icc 0 T)) : InjOn (fun t => gamma (T - t)) (Icc 0 T) := by
  intro s hs t ht he
  have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
    ⟨by linarith [ht.2], by linarith [ht.1]⟩ he
  linarith

private theorem reverse_image (gamma : ℝ → AnnulusCoordinates) (T : ℝ) :
    (fun t => gamma (T - t)) '' Icc 0 T = gamma '' Icc 0 T := by
  change (gamma ∘ fun t => T - t) '' Icc 0 T = _
  rw [image_comp, image_const_sub_Icc]
  simp only [sub_self, sub_zero]

theorem m64Intrinsic_three_arc_reverse_data
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ e, ∀ t ∈ Ioo 0 (T e), deriv (gamma e) t ≠ 0)
    (hsreg : ∀ t ∈ Ioo 0 S, deriv sigma t ≠ 0)
    (hind0 : LinearIndependent ℝ
      (![deriv (gamma false) 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {U : Set AnnulusCoordinates}
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hray : ∀ e, ∀ t ∈ Ioo 0 (T e), ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma e t + r • ((-1 : ℝ) • quarterTurn (deriv (gamma e) t)) ∈ U) :
    let g (e : Bool) (t : ℝ) := gamma (!e) (T (!e) - t)
    let s (t : ℝ) := sigma (S - t)
    let L (e : Bool) := T (!e)
    (∀ e, ContDiff ℝ ∞ (g e)) ∧ ContDiff ℝ ∞ s ∧
      (∀ e, InjOn (g e) (Icc 0 (L e))) ∧ InjOn s (Icc 0 S) ∧
      s 0 = g false 0 ∧ s S = g true (L true) ∧
      g false (L false) = g true 0 ∧
      deriv (g false) (L false) ≠ 0 ∧
      deriv (g true) 0 = speed⁻¹ • deriv (g false) (L false) ∧
      (∀ x ∈ Icc 0 (L false), ∀ y ∈ Icc 0 (L true),
        g false x = g true y → x = L false ∧ y = 0) ∧
      (∀ x ∈ Icc 0 (L false), ∀ y ∈ Icc 0 S, g false x = s y → x = 0 ∧ y = 0) ∧
      (∀ x ∈ Icc 0 (L true), ∀ y ∈ Icc 0 S,
        g true x = s y → x = L true ∧ y = S) ∧
      (∀ e, ∀ t ∈ Ioo 0 (L e), deriv (g e) t ≠ 0) ∧
      (∀ t ∈ Ioo 0 S, deriv s t ≠ 0) ∧
      LinearIndependent ℝ (![deriv (g false) 0, deriv s 0] : Fin 2 → AnnulusCoordinates) ∧
      LinearIndependent ℝ
        (![-deriv (g true) (L true), -deriv s S] : Fin 2 → AnnulusCoordinates) ∧
      frontier U = g false '' Icc 0 (L false) ∪ g true '' Icc 0 (L true) ∪ s '' Icc 0 S ∧
      ∀ e, ∀ t ∈ Ioo 0 (L e), ∀ᶠ r in 𝓝[>] (0 : ℝ),
        g e t + r • quarterTurn (deriv (g e) t) ∈ U := by
  intro g s L
  have hd (e : Bool) (t : ℝ) : deriv (g e) t = -deriv (gamma (!e)) (T (!e) - t) := by
    change deriv (fun t => gamma (!e) (T (!e) - t)) t = _
    rw [deriv_comp_const_sub]
  have hds (t : ℝ) : deriv s t = -deriv sigma (S - t) := by
    change deriv (fun t => sigma (S - t)) t = _
    rw [deriv_comp_const_sub]
  refine ⟨fun e => (hg (!e)).comp (contDiff_const.sub contDiff_id),
    hs.comp (contDiff_const.sub contDiff_id), fun e => reverse_inj (hinj (!e)),
    reverse_inj hsi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [s, g, Bool.not_false, sub_zero] using hend
  · simpa only [s, g, L, Bool.not_true, sub_self] using hstart
  · simpa only [g, L, Bool.not_false, Bool.not_true, sub_self, sub_zero] using hjoin.symm
  · rw [hd]
    change -deriv (gamma true) (T true - T true) ≠ 0
    rw [sub_self, htan]
    exact neg_ne_zero.mpr (smul_ne_zero hspeed.ne' hreg)
  · rw [hd, hd]
    change -deriv (gamma false) (T false - 0) =
      speed⁻¹ • (-deriv (gamma true) (T true - T true))
    rw [sub_zero, sub_self, htan, smul_neg, smul_smul, inv_mul_cancel₀ hspeed.ne', one_smul]
  · intro x hx y hy he
    change x ∈ Icc 0 (T true) at hx
    change y ∈ Icc 0 (T false) at hy
    have hh := hab (T false - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
      (T true - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ he.symm
    exact ⟨by change x = T true; linarith [hh.2], by linarith [hh.1]⟩
  · intro x hx y hy he
    change x ∈ Icc 0 (T true) at hx
    have hh := hbs (T true - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      (S - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩ he
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · intro x hx y hy he
    change x ∈ Icc 0 (T false) at hx
    have hh := has (T false - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      (S - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩ he
    exact ⟨by change x = T false; linarith [hh.1], by linarith [hh.2]⟩
  · intro e t ht
    rw [hd]
    exact neg_ne_zero.mpr (hregular (!e) _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  · intro t ht
    rw [hds]
    exact neg_ne_zero.mpr (hsreg _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  · rw [hd, hds]
    simpa only [Bool.not_false, sub_zero] using hind1
  · rw [hd, hds]
    simpa only [L, Bool.not_true, sub_self, neg_neg] using hind0
  · change frontier U = (fun t => gamma true (T true - t)) '' Icc 0 (T true) ∪
      (fun t => gamma false (T false - t)) '' Icc 0 (T false) ∪
      (fun t => sigma (S - t)) '' Icc 0 S
    rw [reverse_image, reverse_image, reverse_image]
    exact hfront.trans (by ac_rfl)
  · intro e t ht
    simpa only [g, deriv_comp_const_sub, map_neg, neg_one_smul] using
      hray (!e) (T (!e) - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩

end PoincareConjecture
