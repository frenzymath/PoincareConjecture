import PoincareConjecture.Proofs.M38.LowerEndReparametrization
import PoincareConjecture.Proofs.M38.AnnulusReparametrization
import Mathlib.Algebra.Order.GroupWithZero.OrderIso










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private noncomputable def reciprocalBase : ℝ ≃o ℝ :=
  lowerEndOrderIso (1 / 2) (by norm_num) (by norm_num)


noncomputable def reciprocalInnerOrderIso : ℝ ≃o ℝ :=
  (OrderIso.subRight (1 : ℝ)).trans (reciprocalBase.trans (OrderIso.addLeft 1))


noncomputable def reciprocalOuterOrderIso : ℝ ≃o ℝ where
  toFun t := 1 - 2 * reciprocalBase ((1 - t) / 2)
  invFun t := 1 - 2 * reciprocalBase.symm ((1 - t) / 2)
  left_inv t := by
    change 1 - 2 * reciprocalBase.symm
      ((1 - (1 - 2 * reciprocalBase ((1 - t) / 2))) / 2) = t
    rw [show (1 - (1 - 2 * reciprocalBase ((1 - t) / 2))) / 2 =
      reciprocalBase ((1 - t) / 2) by ring, OrderIso.symm_apply_apply]
    ring
  right_inv t := by
    change 1 - 2 * reciprocalBase
      ((1 - (1 - 2 * reciprocalBase.symm ((1 - t) / 2))) / 2) = t
    rw [show (1 - (1 - 2 * reciprocalBase.symm ((1 - t) / 2))) / 2 =
      reciprocalBase.symm ((1 - t) / 2) by ring, OrderIso.apply_symm_apply]
    ring
  map_rel_iff' := by
    intro a b
    change 1 - 2 * reciprocalBase ((1 - a) / 2) ≤
      1 - 2 * reciprocalBase ((1 - b) / 2) ↔ a ≤ b
    constructor
    · intro h
      have hF : reciprocalBase ((1 - b) / 2) ≤ reciprocalBase ((1 - a) / 2) := by
        linarith
      have h' := reciprocalBase.le_iff_le.mp hF
      linarith
    · intro h
      have hF := reciprocalBase.monotone (show (1 - b) / 2 ≤ (1 - a) / 2 by linarith)
      linarith


theorem reciprocalInnerOrderIso_apply (t : ℝ) :
    reciprocalInnerOrderIso t = 1 + lowerEndProfile (1 / 2) (t - 1) := rfl


theorem reciprocalOuterOrderIso_apply (t : ℝ) :
    reciprocalOuterOrderIso t = 1 - 2 * lowerEndProfile (1 / 2) ((1 - t) / 2) := rfl


theorem reciprocalInnerOrderIso_symm_apply (t : ℝ) :
    reciprocalInnerOrderIso.symm t =
      1 + (lowerEndOrderIso (1 / 2) (by norm_num) (by norm_num)).symm (t - 1) := by
  apply reciprocalInnerOrderIso.injective
  rw [OrderIso.apply_symm_apply]
  change t = 1 + reciprocalBase
    (1 + reciprocalBase.symm (t - 1) - 1)
  rw [show 1 + reciprocalBase.symm (t - 1) - 1 =
    reciprocalBase.symm (t - 1) by ring, OrderIso.apply_symm_apply]
  ring


theorem reciprocalOuterOrderIso_symm_apply (t : ℝ) :
    reciprocalOuterOrderIso.symm t =
      1 - 2 * (lowerEndOrderIso (1 / 2) (by norm_num) (by norm_num)).symm
        ((1 - t) / 2) := rfl


theorem reciprocalInnerOrderIso_smooth : ContDiff ℝ ∞ reciprocalInnerOrderIso := by
  change ContDiff ℝ ∞ (fun t : ℝ => 1 + lowerEndProfile (1 / 2) (t - 1))
  exact contDiff_const.add ((lowerEndProfile_smooth (1 / 2)).comp
    (contDiff_id.sub contDiff_const))


theorem reciprocalOuterOrderIso_smooth : ContDiff ℝ ∞ reciprocalOuterOrderIso := by
  change ContDiff ℝ ∞ (fun t : ℝ =>
    1 - 2 * lowerEndProfile (1 / 2) ((1 - t) / 2))
  exact contDiff_const.sub (contDiff_const.mul ((lowerEndProfile_smooth (1 / 2)).comp
    ((contDiff_const.sub contDiff_id).div_const 2)))


theorem reciprocalInnerOrderIso_symm_smooth :
    ContDiff ℝ ∞ reciprocalInnerOrderIso.symm := by
  rw [show (reciprocalInnerOrderIso.symm : ℝ → ℝ) = _ from
    funext reciprocalInnerOrderIso_symm_apply]
  exact contDiff_const.add ((lowerEndOrderIso_symm_smooth
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)).comp
      (contDiff_id.sub contDiff_const))


theorem reciprocalOuterOrderIso_symm_smooth :
    ContDiff ℝ ∞ reciprocalOuterOrderIso.symm := by
  change ContDiff ℝ ∞ (fun t : ℝ =>
    1 - 2 * (lowerEndOrderIso (1 / 2) (by norm_num) (by norm_num)).symm
      ((1 - t) / 2))
  exact contDiff_const.sub (contDiff_const.mul ((lowerEndOrderIso_symm_smooth
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)).comp
      ((contDiff_const.sub contDiff_id).div_const 2)))


theorem reciprocalInnerOrderIso_eq_self {t : ℝ} (ht : t ≤ 1 / 2) :
    reciprocalInnerOrderIso t = t := by
  rw [reciprocalInnerOrderIso_apply, lowerEndProfile_outer (1 / 2) (by
    rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    linarith)]
  ring


theorem reciprocalOuterOrderIso_eq_self {t : ℝ} (ht : t ≤ 1 / 2) :
    reciprocalOuterOrderIso t = t := by
  rw [reciprocalOuterOrderIso_apply, lowerEndProfile_outer (1 / 2) (by
    rw [abs_of_nonneg (by linarith : 0 ≤ (1 - t) / 2)]
    linarith)]
  ring


theorem reciprocalInnerOrderIso_symm_eq_self {t : ℝ} (ht : t ≤ 1 / 2) :
    reciprocalInnerOrderIso.symm t = t := by
  apply reciprocalInnerOrderIso.injective
  rw [OrderIso.apply_symm_apply, reciprocalInnerOrderIso_eq_self ht]


theorem reciprocalOuterOrderIso_symm_eq_self {t : ℝ} (ht : t ≤ 1 / 2) :
    reciprocalOuterOrderIso.symm t = t := by
  apply reciprocalOuterOrderIso.injective
  rw [OrderIso.apply_symm_apply, reciprocalOuterOrderIso_eq_self ht]


@[simp] theorem reciprocalInnerOrderIso_zero : reciprocalInnerOrderIso 0 = 0 :=
  reciprocalInnerOrderIso_eq_self (by norm_num)


@[simp] theorem reciprocalOuterOrderIso_zero : reciprocalOuterOrderIso 0 = 0 :=
  reciprocalOuterOrderIso_eq_self (by norm_num)


@[simp] theorem reciprocalInnerOrderIso_one : reciprocalInnerOrderIso 1 = 1 := by
  change 1 + reciprocalBase (1 - 1) = 1
  have hzero : reciprocalBase 0 = 0 :=
    lowerEndOrderIso_zero (1 / 2) (by norm_num) (by norm_num)
  rw [sub_self, hzero, add_zero]


@[simp] theorem reciprocalOuterOrderIso_one : reciprocalOuterOrderIso 1 = 1 := by
  change 1 - 2 * reciprocalBase ((1 - 1) / 2) = 1
  have hzero : reciprocalBase 0 = 0 :=
    lowerEndOrderIso_zero (1 / 2) (by norm_num) (by norm_num)
  rw [sub_self, zero_div, hzero, mul_zero, sub_zero]


theorem reciprocalInnerOrderIso_annulus {s : ℝ} (hs : |s| ≤ 1 / 8) :
    reciprocalInnerOrderIso (1 - s) = (1 + s / 2) / (1 + s) := by
  have hden : 1 + s ≠ 0 := by have h := (abs_le.mp hs).1; linarith
  rw [reciprocalInnerOrderIso_apply, show 1 - s - 1 = -s by ring,
    lowerEndProfile_inner (1 / 2) (by simpa only [abs_neg] using hs)]
  rw [sub_neg_eq_add]
  field_simp [hden]
  ring


theorem reciprocalOuterOrderIso_annulus {s : ℝ} (hs : |s| ≤ 1 / 8) :
    reciprocalOuterOrderIso (1 + s) = (1 + s) / (1 + s / 2) := by
  have hden : 1 + s / 2 ≠ 0 := by have h := (abs_le.mp hs).1; linarith
  have htwo : 2 + s ≠ 0 := by have h := (abs_le.mp hs).1; linarith
  have hsmall : |(1 - (1 + s)) / 2| ≤ 1 / 8 := by
    rw [abs_le]
    have h := abs_le.mp hs
    constructor <;> linarith
  rw [reciprocalOuterOrderIso_apply, lowerEndProfile_inner (1 / 2) hsmall]
  have heq : 1 - (1 - (1 + s)) / 2 = 1 + s / 2 := by ring
  rw [heq]
  field_simp [hden, htwo]
  ring


theorem reciprocalOrderIso_annulus_product {s : ℝ} (hs : |s| ≤ 1 / 8) :
    reciprocalInnerOrderIso (1 - s) * reciprocalOuterOrderIso (1 + s) = 1 := by
  have h := abs_le.mp hs
  rw [reciprocalInnerOrderIso_annulus hs, reciprocalOuterOrderIso_annulus hs]
  field_simp [show 1 + s ≠ 0 by linarith, show 1 + s / 2 ≠ 0 by linarith,
    show 2 + s ≠ 0 by linarith]


theorem reciprocalInnerOrderIso_nine_eighths :
    reciprocalInnerOrderIso (9 / 8) = 15 / 14 := by
  have h := reciprocalInnerOrderIso_annulus (s := -1 / 8) (by norm_num)
  norm_num at h
  exact h


theorem reciprocalOuterOrderIso_nine_eighths :
    reciprocalOuterOrderIso (9 / 8) = 18 / 17 := by
  have h := reciprocalOuterOrderIso_annulus (s := 1 / 8) (by norm_num)
  norm_num at h
  exact h

private theorem radialOrderIso_symm_zero (e : ℝ ≃o ℝ) (he0 : e 0 = 0) : e.symm 0 = 0 := by
  apply e.injective
  rw [OrderIso.apply_symm_apply, he0]

private noncomputable def reciprocalRadialDiffeomorph (e : ℝ ≃o ℝ)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hfix : ∀ t, t ≤ 1 / 2 → e t = t) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ := by
  have he0 : e 0 = 0 := hfix 0 (by norm_num)
  have hifix (t : ℝ) (ht : t ≤ 1 / 2) : e.symm t = t := by
    apply e.injective
    rw [OrderIso.apply_symm_apply, hfix t ht]
  exact {
    toFun := capRadialMap e
    invFun := capRadialMap e.symm
    left_inv := capRadialMap_left_inverse e he0
    right_inv := capRadialMap_left_inverse e.symm (radialOrderIso_symm_zero e he0)
    contMDiff_toFun := contMDiff_iff_contDiff.mpr
      (capRadialMap_smooth e he (1 / 2) 1 (by norm_num)
        (fun t ht => by simpa only [one_mul] using hfix t ht))
    contMDiff_invFun := contMDiff_iff_contDiff.mpr
      (capRadialMap_smooth e.symm hi (1 / 2) 1 (by norm_num)
        (fun t ht => by simpa only [one_mul] using hifix t ht)) }


noncomputable def reciprocalInnerRadial :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  reciprocalRadialDiffeomorph reciprocalInnerOrderIso reciprocalInnerOrderIso_smooth
    reciprocalInnerOrderIso_symm_smooth (fun _ => reciprocalInnerOrderIso_eq_self)


noncomputable def reciprocalOuterRadial :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  reciprocalRadialDiffeomorph reciprocalOuterOrderIso reciprocalOuterOrderIso_smooth
    reciprocalOuterOrderIso_symm_smooth (fun _ => reciprocalOuterOrderIso_eq_self)


theorem reciprocalInnerRadial_apply (x : StandardCapSpace) :
    reciprocalInnerRadial x = capRadialMap reciprocalInnerOrderIso x := rfl


theorem reciprocalOuterRadial_apply (x : StandardCapSpace) :
    reciprocalOuterRadial x = capRadialMap reciprocalOuterOrderIso x := rfl


theorem reciprocalInnerRadial_norm (x : StandardCapSpace) :
    ‖reciprocalInnerRadial x‖ = reciprocalInnerOrderIso ‖x‖ :=
  capRadialMap_norm _ reciprocalInnerOrderIso_zero
    (fun t ht => by simpa using reciprocalInnerOrderIso.monotone ht) x


theorem reciprocalOuterRadial_norm (x : StandardCapSpace) :
    ‖reciprocalOuterRadial x‖ = reciprocalOuterOrderIso ‖x‖ :=
  capRadialMap_norm _ reciprocalOuterOrderIso_zero
    (fun t ht => by simpa using reciprocalOuterOrderIso.monotone ht) x

private theorem reciprocalRadial_closedBall
    (e : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞)
    (f : ℝ ≃o ℝ) (hf1 : f 1 = 1) (hnorm : ∀ x, ‖e x‖ = f ‖x‖) :
    e '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have himage : e x ∈ e '' Metric.closedBall 0 1 ↔ x ∈ Metric.closedBall 0 1 :=
    e.injective.mem_set_image
  change e x ∈ e '' Metric.closedBall 0 1 ↔ e x ∈ Metric.closedBall 0 1
  rw [himage]
  simp only [Metric.mem_closedBall, dist_zero_right, hnorm]
  simpa only [hf1] using
    (show f ‖x‖ ≤ f 1 ↔ ‖x‖ ≤ 1 from f.le_iff_le).symm


theorem reciprocalInnerRadial_closedBall :
    reciprocalInnerRadial '' Metric.closedBall 0 1 = Metric.closedBall 0 1 :=
  reciprocalRadial_closedBall _ _ reciprocalInnerOrderIso_one reciprocalInnerRadial_norm


theorem reciprocalOuterRadial_closedBall :
    reciprocalOuterRadial '' Metric.closedBall 0 1 = Metric.closedBall 0 1 :=
  reciprocalRadial_closedBall _ _ reciprocalOuterOrderIso_one reciprocalOuterRadial_norm

private theorem capRadialMap_ray (f : ℝ → ℝ) (z : UnitTwoSphere)
    {t : ℝ} (ht : 0 < t) : capRadialMap f (t • z.val) = f t • z.val := by
  rw [capRadialMap, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    show ‖z.val‖ = 1 by simp, mul_one, smul_smul, div_mul_cancel₀ _ ht.ne']


theorem reciprocalInnerRadial_ray (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    reciprocalInnerRadial (t • z.val) = reciprocalInnerOrderIso t • z.val :=
  capRadialMap_ray _ z ht


theorem reciprocalOuterRadial_ray (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    reciprocalOuterRadial (t • z.val) = reciprocalOuterOrderIso t • z.val :=
  capRadialMap_ray _ z ht

private theorem reciprocalAnnulus_lt_one {a : ℝ} (ha8 : a ≤ 1 / 8) : a < 1 := by
  linarith

variable {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)

include ha ha8


noncomputable def reciprocalInnerBallDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  ((capRadialDiffeomorph 1 a ha (reciprocalAnnulus_lt_one ha8)).trans
    reciprocalInnerRadial).trans
      ((LinearEquiv.smulOfNeZero ℝ StandardCapSpace (3 / 2 : ℝ)
        (by norm_num)).toContinuousLinearEquiv.toDiffeomorph)


noncomputable def reciprocalOuterBallDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  ((capRadialDiffeomorph 1 a ha (reciprocalAnnulus_lt_one ha8)).trans
    reciprocalOuterRadial).trans
      ((LinearEquiv.smulOfNeZero ℝ StandardCapSpace (8 / 3 : ℝ)
        (by norm_num)).toContinuousLinearEquiv.toDiffeomorph)


theorem reciprocalInnerBallDiffeomorph_apply (x : StandardCapSpace) :
    reciprocalInnerBallDiffeomorph ha ha8 x =
      (3 / 2 : ℝ) • reciprocalInnerRadial
        (capRadialDiffeomorph 1 a ha (reciprocalAnnulus_lt_one ha8) x) := rfl


theorem reciprocalOuterBallDiffeomorph_apply (x : StandardCapSpace) :
    reciprocalOuterBallDiffeomorph ha ha8 x =
      (8 / 3 : ℝ) • reciprocalOuterRadial
        (capRadialDiffeomorph 1 a ha (reciprocalAnnulus_lt_one ha8) x) := rfl


theorem reciprocalInnerBallDiffeomorph_norm (x : StandardCapSpace) :
    ‖reciprocalInnerBallDiffeomorph ha ha8 x‖ =
      (3 / 2) * reciprocalInnerOrderIso (capRadialProfile 1 a ‖x‖) := by
  rw [reciprocalInnerBallDiffeomorph_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), reciprocalInnerRadial_norm,
    capRadialDiffeomorph_norm]


theorem reciprocalOuterBallDiffeomorph_norm (x : StandardCapSpace) :
    ‖reciprocalOuterBallDiffeomorph ha ha8 x‖ =
      (8 / 3) * reciprocalOuterOrderIso (capRadialProfile 1 a ‖x‖) := by
  rw [reciprocalOuterBallDiffeomorph_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 8 / 3), reciprocalOuterRadial_norm,
    capRadialDiffeomorph_norm]

private theorem reciprocalCompressedRadius_lt {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 2) : capRadialProfile 1 a ‖x‖ < 9 / 8 := by
  have hm : capRadialDiffeomorph 1 a ha (reciprocalAnnulus_lt_one ha8) x ∈
      Metric.ball 0 (1 + a) := by
    rw [← capRadialDiffeomorph_ball_two ha (reciprocalAnnulus_lt_one ha8)]
    exact Set.mem_image_of_mem _ hx
  have hnorm : capRadialProfile 1 a ‖x‖ < 1 + a := by
    simpa only [Metric.mem_ball, dist_zero_right, capRadialDiffeomorph_norm] using hm
  linarith


theorem reciprocalInnerBallDiffeomorph_bound {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 2) : ‖reciprocalInnerBallDiffeomorph ha ha8 x‖ < 45 / 28 := by
  have h := reciprocalInnerOrderIso.strictMono (reciprocalCompressedRadius_lt ha ha8 hx)
  rw [reciprocalInnerOrderIso_nine_eighths] at h
  rw [reciprocalInnerBallDiffeomorph_norm]
  linarith


theorem reciprocalInnerBallDiffeomorph_mapsTo :
    Set.MapsTo (reciprocalInnerBallDiffeomorph ha ha8) (Metric.ball 0 2) (Metric.ball 0 2) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  have h := reciprocalInnerBallDiffeomorph_bound ha ha8 hx
  linarith


theorem reciprocalOuterBallDiffeomorph_profile_bound {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 2) :
    reciprocalOuterOrderIso (capRadialProfile 1 a ‖x‖) < 18 / 17 := by
  have h := reciprocalOuterOrderIso.strictMono (reciprocalCompressedRadius_lt ha ha8 hx)
  rwa [reciprocalOuterOrderIso_nine_eighths] at h


theorem reciprocalOuterBallDiffeomorph_bound {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 2) : ‖reciprocalOuterBallDiffeomorph ha ha8 x‖ < 48 / 17 := by
  rw [reciprocalOuterBallDiffeomorph_norm]
  have h := reciprocalOuterBallDiffeomorph_profile_bound ha ha8 hx
  linarith

private theorem reciprocal_scaled_closedBall
    (e : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞)
    (f : ℝ ≃o ℝ) (hf1 : f 1 = 1) (r : ℝ) (hr : 0 < r)
    (hnorm : ∀ x, ‖e x‖ = r * f (capRadialProfile 1 a ‖x‖)) :
    e '' Metric.closedBall 0 1 = Metric.closedBall 0 r := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have himage : e x ∈ e '' Metric.closedBall 0 1 ↔ x ∈ Metric.closedBall 0 1 :=
    e.injective.mem_set_image
  change e x ∈ e '' Metric.closedBall 0 1 ↔ e x ∈ Metric.closedBall 0 r
  rw [himage]
  simp only [Metric.mem_closedBall, dist_zero_right, hnorm]
  have hc := capRadialProfile_strictMono ha (reciprocalAnnulus_lt_one ha8)
  constructor
  · intro hx
    have hp : capRadialProfile 1 a ‖x‖ ≤ 1 := by
      simpa only [capRadialProfile_one] using hc.monotone hx
    have hf : f (capRadialProfile 1 a ‖x‖) ≤ 1 := by
      simpa only [hf1] using f.monotone hp
    nlinarith
  · intro hx
    have hf : f (capRadialProfile 1 a ‖x‖) ≤ f 1 := by
      rw [hf1]
      nlinarith
    have hp := f.le_iff_le.mp hf
    exact hc.le_iff_le.mp (by simpa only [capRadialProfile_one] using hp)


theorem reciprocalInnerBallDiffeomorph_closedBall :
    reciprocalInnerBallDiffeomorph ha ha8 '' Metric.closedBall 0 1 =
      Metric.closedBall 0 (3 / 2) :=
  reciprocal_scaled_closedBall ha ha8 _ _ reciprocalInnerOrderIso_one (3 / 2)
    (by norm_num) (reciprocalInnerBallDiffeomorph_norm ha ha8)


theorem reciprocalOuterBallDiffeomorph_closedBall :
    reciprocalOuterBallDiffeomorph ha ha8 '' Metric.closedBall 0 1 =
      Metric.closedBall 0 (8 / 3) :=
  reciprocal_scaled_closedBall ha ha8 _ _ reciprocalOuterOrderIso_one (8 / 3)
    (by norm_num) (reciprocalOuterBallDiffeomorph_norm ha ha8)

private theorem reciprocalParameter_bound {s : ℝ} (hs : |s| < 1) : |a * s| ≤ 1 / 8 := by
  rw [abs_mul, abs_of_pos ha]
  have h := mul_lt_mul_of_pos_left hs ha
  linarith


theorem reciprocalInnerBallDiffeomorph_negative (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    reciprocalInnerBallDiffeomorph ha ha8 ((1 - s) • z.val) =
      ((3 / 2) * ((1 + a * s / 2) / (1 + a * s))) • z.val := by
  rw [reciprocalInnerBallDiffeomorph_apply,
    capRadialDiffeomorph_smul ha (reciprocalAnnulus_lt_one ha8) z (1 - s)
      (by linarith [hs.2])]
  have harg : 1 + a * (1 - s - 1) = 1 - a * s := by ring
  rw [harg, reciprocalInnerRadial_ray z (by nlinarith [hs.2]),
    reciprocalInnerOrderIso_annulus (reciprocalParameter_bound ha ha8
      (abs_lt.mpr ⟨hs.1, by linarith [hs.2]⟩)), smul_smul]


theorem reciprocalOuterBallDiffeomorph_positive (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    reciprocalOuterBallDiffeomorph ha ha8 ((1 + s) • z.val) =
      ((8 / 3) * ((1 + a * s) / (1 + a * s / 2))) • z.val := by
  rw [reciprocalOuterBallDiffeomorph_apply,
    capRadialDiffeomorph_smul ha (reciprocalAnnulus_lt_one ha8) z (1 + s)
      (by linarith [hs.1]), add_sub_cancel_left,
    reciprocalOuterRadial_ray z (by nlinarith [mul_pos ha hs.1]),
    reciprocalOuterOrderIso_annulus (reciprocalParameter_bound ha ha8
      (abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩)), smul_smul]

end PoincareConjecture.M38
