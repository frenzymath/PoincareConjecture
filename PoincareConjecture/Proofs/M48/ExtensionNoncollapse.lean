import PoincareConjecture.Proofs.M48.ExtensionCanonical
import PoincareConjecture.Definitions.Ch16.ControlledSurgery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)

theorem canonical_on (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    {J : Set ℝ} {r : ℝ} (hJ : J ⊆ F.time_domain)
    (h : SurgeryCanonicalOn F J r) : SurgeryCanonicalOn E.extended J r := by
  intro t ht _ x hx
  let f := E.identify t (hJ ht)
  obtain ⟨y, rfl⟩ := f.surjective x
  have H := E.metric_calculus m13 t (hJ ht)
  have hy : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y := by
    rw [H.m48_scalar_eq (F.connection t) (E.extended.connection t)]
    exact hx
  change SurgeryCanonicalControl E.extended t (E.identify t (hJ ht) y)
    E.extended.parameters.epsilon E.extended.parameters.C
  simpa only [E.parameters_eq] using
    E.canonical_control m13 t (hJ ht) y _ _ (h t ht (hJ ht) y hy)

theorem noncollapsed_on (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    {J : Set ℝ} {kappa : ℝ} (hJ : J ⊆ F.time_domain)
    (h : SurgeryNoncollapsedOn F J kappa) : SurgeryNoncollapsedOn E.extended J kappa := by
  intro t ht _ x hpositive r hr hrepsilon d hterminal hcurvature
  let f := E.identify t (hJ ht)
  obtain ⟨x, rfl⟩ := f.surjective x
  have H : MetricHomothetyCalculus (F.metric t) (E.extended.metric t) f 1 :=
    E.metric_calculus m13 t (hJ ht)
  have htime : ∀ s ∈ Icc (-r ^ 2) 0, t + s / 1 ∈ F.time_domain := by
    intro s hs
    have hn := E.extended.time_domain_nonnegative (d.time_subset ⟨s, hs, rfl⟩)
    exact F.time_domain_interval.out F.zero_mem (hJ ht)
      ⟨hn, by simpa only [div_one, add_le_iff_nonpos_right] using hs.2⟩
  have hball : (F.metric t).ball x r ⊆ f ⁻¹' (E.extended.metric t).ball (f x) r :=
    (H.m48_ball_eq x r).subset
  let c := ((E.pullCylinder d htime).rebaseSource f).restrictSource hball
  have hc : ∀ h y, y ∈ (F.metric t).ball x r → HEq (c.forward 0 h y) y := by
    intro h y hy
    have hz := E.identify_symm_heq (htime 0 h) (hJ ht) (by simp)
      (hterminal h (f y) (hball hy))
    change HEq (c.forward 0 h y) (f.symm (f y)) at hz
    simpa only [f.symm_apply_apply] using hz
  have hbound : ∀ s hs y, y ∈ (F.metric t).ball x r →
      (F.connection (t + s / 1)).curvatureTensorNorm (c.forward s hs y) ≤ r⁻¹ ^ 2 := by
    intro s hs y hy
    let e := E.identify (t + s / 1) (htime s hs)
    have hc := (E.metric_calculus m13 (t + s / 1) (htime s hs)).curvature_norm_eq
      (F.connection (t + s / 1)) (E.extended.connection (t + s / 1))
      (e.symm (d.forward s hs (f y)))
    have hc' : (E.extended.connection (t + s / 1)).curvatureTensorNorm
        (d.forward s hs (f y)) =
        (F.connection (t + s / 1)).curvatureTensorNorm (c.forward s hs y) := by
      change (E.extended.connection (t + s / 1)).curvatureTensorNorm
        (d.forward s hs (f y)) =
        (F.connection (t + s / 1)).curvatureTensorNorm (e.symm (d.forward s hs (f y)))
      simpa only [e, Diffeomorph.apply_symm_apply, div_one] using hc
    rw [← hc']
    exact hcurvature s hs (f y) (hball hy)
  have hr' : r ≤ F.parameters.epsilon := by
    simpa only [E.parameters_eq] using hrepsilon
  have hv := h t ht (hJ ht) x
    (fun hp => hpositive (E.positive_component m13 t (hJ ht) x hp))
    r hr hr' c hc hbound
  rw [H.m48_ball_eq x r, H.m48_volume_eq] at hv
  exact hv

end PoincareConjecture.SurgeryFlowExtension
