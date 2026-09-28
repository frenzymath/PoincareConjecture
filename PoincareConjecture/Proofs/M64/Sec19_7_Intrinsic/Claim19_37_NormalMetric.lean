import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalGauss













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem m64Intrinsic_geodesic_velocity_unit
    (N : IntrinsicAnnulus) {q : ℝ → AnnulusCoordinates} {I : Set ℝ} {b : ℝ}
    (hb : 0 < b) (hgeo : N.metric.IsGeodesicOn q I) (hsub : Icc (0 : ℝ) b ⊆ I)
    (hzero : N.metric.inner (q 0) (curveVelocity (n := 2) q 0)
      (curveVelocity (n := 2) q 0) = 1) :
    ∀ t ∈ Icc (0 : ℝ) b,
      N.metric.inner (q t) (curveVelocity (n := 2) q t) (curveVelocity (n := 2) q t) = 1 := by
  let speed : ℝ → ℝ := fun t => N.metric.tangentNorm (q t) (curveVelocity (n := 2) q t)
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) : HasDerivAt speed 0 t :=
    hgeo.hasDerivAt_tangentNorm_zero (hsub ht)
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hs0 : speed 0 = 1 := by
    change Real.sqrt (N.metric.inner (q 0)
      (curveVelocity (n := 2) q 0) (curveVelocity (n := 2) q 0)) = 1
    rw [hzero, Real.sqrt_one]
  intro t ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs' => (hs s hs').hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (convex_Icc (0 : ℝ) b) hz ht
  have heq : speed t = 1 := by
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, hs0] using h
  change Real.sqrt (N.metric.inner (q t)
    (curveVelocity (n := 2) q t) (curveVelocity (n := 2) q t)) = 1 at heq
  have hpos := (Real.sqrt_pos.mp (show 0 < Real.sqrt _ from heq.symm ▸ zero_lt_one)).le
  have hsq := Real.sq_sqrt hpos
  rw [heq] at hsq
  simpa only [one_pow] using hsq.symm




theorem m64Intrinsic_normal_variation_metric
    (N : IntrinsicAnnulus) {u : ℝ × ℝ → AnnulusCoordinates} {a t : ℝ}
    (hu : DifferentiableAt ℝ u (a, t))
    (hunit : N.metric.inner (u (a, t))
      (curveVelocity (n := 2) (fun r => u (a, r)) t)
      (curveVelocity (n := 2) (fun r => u (a, r)) t) = 1)
    (horth : N.metric.inner (u (a, t))
      (curveVelocity (n := 2) (fun r => u (a, r)) t)
      (curveVelocity (n := 2) (fun s => u (s, t)) a) = 0)
    (v : ℝ × ℝ) :
    N.metric.inner (u (a, t)) (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v) =
      v.1 ^ 2 * N.metric.inner (u (a, t))
        (curveVelocity (n := 2) (fun s => u (s, t)) a)
        (curveVelocity (n := 2) (fun s => u (s, t)) a) + v.2 ^ 2 := by
  let X : AnnulusCoordinates := curveVelocity (n := 2) (fun s => u (s, t)) a
  let T : AnnulusCoordinates := curveVelocity (n := 2) (fun r => u (a, r)) t
  let L := fderiv ℝ u (a, t)
  change N.metric.inner (u (a, t)) T T = 1 at hunit
  change N.metric.inner (u (a, t)) T X = 0 at horth
  have hfst : L (1, 0) = X := by
    have h := hu.hasFDerivAt.comp_hasDerivAt (l := u) (f := fun s => (s, t)) a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const a t))
    exact h.deriv.symm.trans (m64Intrinsic_curveVelocity_eq_deriv _ _).symm
  have hsnd : L (0, 1) = T := by
    have h := hu.hasFDerivAt.comp_hasDerivAt (l := u) (f := fun r => (a, r)) t
      ((hasDerivAt_const t a).prodMk (hasDerivAt_id t))
    exact h.deriv.symm.trans (m64Intrinsic_curveVelocity_eq_deriv _ _).symm
  have hL : L v = v.1 • X + v.2 • T := by
    have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
    calc
      L v = L (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg L hv
      _ = _ := by rw [map_add, map_smul, map_smul, hfst, hsnd]
  have horth' : N.metric.inner (u (a, t)) X T = 0 := by
    rw [N.metric.symm]
    exact horth
  change N.metric.inner (u (a, t)) (L v) (L v) = _
  rw [hL]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    horth', horth, hunit, mul_zero, mul_one, zero_add, add_zero]
  ring




theorem m64Intrinsic_normal_variation_metric_lower
    (N : IntrinsicAnnulus) {u : ℝ × ℝ → AnnulusCoordinates} {a t c speed : ℝ}
    (hu : DifferentiableAt ℝ u (a, t)) (hc : 0 < c) (hc1 : c ≤ 1) (hspeed : 0 < speed)
    (hunit : N.metric.inner (u (a, t))
      (curveVelocity (n := 2) (fun r => u (a, r)) t)
      (curveVelocity (n := 2) (fun r => u (a, r)) t) = 1)
    (horth : N.metric.inner (u (a, t))
      (curveVelocity (n := 2) (fun r => u (a, r)) t)
      (curveVelocity (n := 2) (fun s => u (s, t)) a) = 0)
    (hlower : c * speed ≤ N.metric.tangentNorm (u (a, t))
      (curveVelocity (n := 2) (fun s => u (s, t)) a)) :
    (∀ v : ℝ × ℝ,
      c ^ 2 * (speed ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
        N.metric.inner (u (a, t)) (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
      Function.Injective (fderiv ℝ u (a, t)) := by
  let X : AnnulusCoordinates := curveVelocity (n := 2) (fun s => u (s, t)) a
  have hpositive : 0 < N.metric.tangentNorm (u (a, t)) X :=
    (mul_pos hc hspeed).trans_le hlower
  have hxx : 0 ≤ N.metric.inner (u (a, t)) X X := (Real.sqrt_pos.mp hpositive).le
  have hsq : c ^ 2 * speed ^ 2 ≤ N.metric.inner (u (a, t)) X X := by
    have hnormsq := Real.sq_sqrt hxx
    change (N.metric.tangentNorm (u (a, t)) X) ^ 2 = _ at hnormsq
    nlinarith [mul_pos hc hspeed]
  have hbound (v : ℝ × ℝ) :
      c ^ 2 * (speed ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
        N.metric.inner (u (a, t)) (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v) := by
    rw [m64Intrinsic_normal_variation_metric N hu hunit horth v]
    have hx := mul_le_mul_of_nonneg_left hsq (sq_nonneg v.1)
    have hc2 : c ^ 2 ≤ 1 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hc2 (sq_nonneg v.2)
    nlinarith
  refine ⟨hbound, (injective_iff_map_eq_zero (fderiv ℝ u (a, t))).mpr ?_⟩
  intro v hv
  have h := hbound v
  rw [hv, map_zero] at h
  have hz : speed ^ 2 * v.1 ^ 2 + v.2 ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp (by simpa only [mul_zero] using h)
  have hv2 : v.2 = 0 := by nlinarith [mul_nonneg (sq_nonneg speed) (sq_nonneg v.1)]
  have hv1 : v.1 = 0 := by
    have hx : speed ^ 2 * v.1 ^ 2 ≤ 0 := by nlinarith
    have hvs : v.1 ^ 2 ≤ 0 := by
      exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hspeed)).mp
        (by simpa only [mul_zero] using hx)
    nlinarith [sq_nonneg v.1]
  exact Prod.ext hv1 hv2

end PoincareConjecture
