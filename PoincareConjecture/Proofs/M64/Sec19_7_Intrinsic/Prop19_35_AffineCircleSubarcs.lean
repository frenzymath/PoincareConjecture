import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RawInnerNormalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

private theorem affine_image_Icc (x d l u : ℝ) (hlu : l ≤ u) :
    (fun t => x + d * t) '' Icc l u =
      Icc (min (x + d * l) (x + d * u)) (max (x + d * l) (x + d * u)) := by
  change ((fun t => x + t) ∘ fun t => d * t) '' Icc l u = _
  rw [← uIcc_of_le hlu, image_comp, image_const_mul_uIcc, image_const_add_uIcc]
  rfl






theorem m64Intrinsic_affine_inner_circle_properties
    (N : IntrinsicAnnulus) (x d : ℝ) (hd : d ≠ 0) :
    let base := fun t : ℝ => intrinsicAnnulusBoundary 1 (x + d * t)
    ContDiff ℝ ∞ base ∧
      (∀ t, deriv base t = d • deriv (intrinsicAnnulusBoundary 1) (x + d * t)) ∧
      (∀ t, ‖base t‖ = 1) ∧ ∀ t, deriv base t ≠ 0 := by
  intro base
  have hderiv (t : ℝ) : deriv base t =
      d • deriv (intrinsicAnnulusBoundary 1) (x + d * t) := by
    have hp : HasDerivAt (fun t : ℝ => x + d * t) d t := by
      simpa only [mul_one] using! ((hasDerivAt_id t).const_mul d).const_add x
    exact (((m64Intrinsic_contDiff_boundary 1).differentiable (by simp)
      (x + d * t)).hasDerivAt.scomp t hp).deriv
  refine ⟨(m64Intrinsic_contDiff_boundary 1).comp (by fun_prop), hderiv,
    fun t => m64Intrinsic_inner_boundary_norm _, ?_⟩
  intro t
  rw [hderiv]
  apply smul_ne_zero hd
  intro hz
  have hpos := m64Intrinsic_boundarySpeed_pos N one_ne_zero (x + d * t)
  simp only [intrinsicBoundarySpeed, RiemannianMetric.tangentNorm,
    m64Intrinsic_curveVelocity_eq_deriv, hz, map_zero, Real.sqrt_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos







theorem m64Intrinsic_affine_inner_circle_subarc
    (N : IntrinsicAnnulus) {x d D r l u : ℝ} (hD : 0 ≤ D)
    (hl : l ∈ Icc 0 D) (hu : u ∈ Icc 0 D) (hlu : l ≤ u)
    (hperiod : |d * D| < rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 (min x (x + d * D))
      (max x (x + d * D)) ≤ r) :
    ∃ a b : ℝ, a ≤ b ∧ b ≤ a + rampPeriod ∧
      InjOn (intrinsicAnnulusBoundary 1) (Icc a b) ∧
      (fun t => intrinsicAnnulusBoundary 1 (x + d * t)) '' Icc l u =
        intrinsicAnnulusBoundary 1 '' Icc a b ∧
      intrinsicBoundaryLength N.metric 1 a b ≤ r := by
  let a := min (x + d * l) (x + d * u)
  let b := max (x + d * l) (x + d * u)
  let a0 := min x (x + d * D)
  let b0 := max x (x + d * D)
  have hab : a ≤ b := min_le_max
  have hfull : (fun t => x + d * t) '' Icc (0 : ℝ) D = Icc a0 b0 := by
    simpa only [mul_zero, add_zero] using affine_image_Icc x d 0 D hD
  have hsub : Icc a b ⊆ Icc a0 b0 := by
    rw [← affine_image_Icc x d l u hlu, ← hfull]
    exact image_mono (Icc_subset_Icc hl.1 hu.2)
  have ha0 : a0 ≤ a := (hsub (left_mem_Icc.mpr hab)).1
  have hb0 : b ≤ b0 := (hsub (right_mem_Icc.mpr hab)).2
  have hwidth : b0 - a0 < rampPeriod := by
    simpa only [b0, a0, max_sub_min_eq_abs, add_sub_cancel_left] using hperiod
  have hwidth' : b - a < rampPeriod := by linarith
  have hcircle := m64Intrinsic_boundary_injOn_short_arc hwidth'
  have himage : (fun t => intrinsicAnnulusBoundary 1 (x + d * t)) '' Icc l u =
      intrinsicAnnulusBoundary 1 '' Icc a b := by
    change (intrinsicAnnulusBoundary 1 ∘ fun t => x + d * t) '' Icc l u = _
    rw [image_comp, affine_image_Icc x d l u hlu]
  have hquant := m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero ha0 hab hb0
  have hnonneg := m64Intrinsic_boundaryLength_nonneg N 1 a0 a ha0
  refine ⟨a, b, hab, by linarith, hcircle, himage, ?_⟩
  change intrinsicBoundaryLength N.metric 1 a0 b0 ≤ r at hshort
  linarith only [hquant.1, hnonneg, hshort]

end PoincareConjecture
