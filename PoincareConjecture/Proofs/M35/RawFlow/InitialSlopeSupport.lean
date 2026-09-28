import PoincareConjecture.Proofs.M35.RawFlow.InitialCylinderNull
import PoincareConjecture.Proofs.M35.RawFlow.AxisRicciForm
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarpingBounds











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness



theorem initial_intrinsic_slope_support (g₀ : StandardInitialMetric)
    (H : StandardCapEstimate g₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ s, R ≤ s →
      deriv (intrinsicWarpingRadius g₀.metric g₀.rotation_invariant g₀.complete) s = 0 := by
  let f := intrinsicWarpingRadius g₀.metric g₀.rotation_invariant g₀.complete
  let p := deriv f
  let q := (radialArclengthOrderIso g₀.metric g₀.rotation_invariant g₀.complete).symm
  obtain ⟨r₀, hr₀, htail⟩ := initial_axis_tail_ricci_null g₀.cylindrical_end g₀.connection
  let s₀ := radialArclength g₀.metric r₀
  have hs₀ : 0 < s₀ := by
    have hh := radialArclength_strictMono g₀.metric hr₀
    rwa [radialArclength_zero] at hh
  have hq (s : ℝ) : radialArclength g₀.metric (q s) = s :=
    (radialArclengthOrderIso g₀.metric g₀.rotation_invariant g₀.complete).apply_symm_apply s
  have hzero (s : ℝ) (hs : s₀ < s) : deriv p s = 0 := by
    have hspos : 0 < s := hs₀.trans hs
    have hr : 0 < q s := radialArclengthOrderIso_symm_pos g₀.metric
      g₀.rotation_invariant g₀.complete hspos
    have hrlarge : r₀ ≤ q s := by
      apply (radialArclength_strictMono g₀.metric).le_iff_le.mp
      rw [hq]
      exact hs.le
    obtain ⟨v, hv, hnull⟩ := htail (q s) hrlarge
    have hK := radialMixedCurvatureFactor_eq_zero_of_ricci_null g₀.connection
      g₀.rotation_invariant g₀.nonnegative_sectional hr hv hnull
    have hsecond := (intrinsicWarpingRadius_deriv_hasDerivAt g₀.metric
      g₀.rotation_invariant g₀.complete hspos).deriv
    change deriv p s = axisWarpingSecond g₀.metric (q s) at hsecond
    rw [hsecond, axisWarpingSecond, hK, mul_zero, zero_div]
  have hp : ContDiff ℝ ∞ p := (contDiff_infty_iff_deriv.mp
    (intrinsicWarpingRadius_contDiff g₀.metric g₀.rotation_invariant g₀.complete)).2
  have hconst {s z : ℝ} (hs : s₀ < s) (hz : s₀ < z) : p s = p z :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi s₀).isPreconnected
      (hp.differentiable (by simp)).differentiableOn (fun x hx => hzero x hx) hs hz
  have hbounds (s : ℝ) (hs : 0 < s) :
      f s ^ 2 ≤ 2 * H.scalar_constant ∧ 0 ≤ p s ∧ s * p s ≤ f s := by
    have hr : 0 < q s := radialArclengthOrderIso_symm_pos g₀.metric
      g₀.rotation_invariant g₀.complete hs
    have hfirst : p s = axisWarpingSlope g₀.metric (q s) :=
      (intrinsicWarpingRadius_hasDerivAt g₀.metric g₀.rotation_invariant g₀.complete hs).deriv
    have hrad := axisWarpingRadius_sq_le_of_exterior_scalar_floor g₀.connection
      g₀.rotation_invariant g₀.complete g₀.nonnegative_sectional
      (inv_pos.mpr H.scalar_constant_pos) (K := ∅) isCompact_empty
      (fun x _ => (H.scalar_bounds x).1) hr
    have hprod := axisWarpingSlope_mul_arclength_le g₀.connection
      g₀.rotation_invariant g₀.nonnegative_sectional hr
    rw [hq, mul_comm, ← hfirst] at hprod
    refine ⟨?_, ?_, hprod⟩
    · change axisWarpingRadius g₀.metric (q s) ^ 2 ≤ 2 * H.scalar_constant
      simpa only [div_inv_eq_mul] using hrad
    · rw [hfirst]
      exact axisWarpingSlope_nonneg g₀.connection g₀.rotation_invariant
        g₀.nonnegative_sectional g₀.complete hr
  let R := s₀ + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  refine ⟨R, hR, ?_⟩
  intro s hs
  have hspos : 0 < s := hR.trans_le hs
  have hstail : s₀ < s := by dsimp only [R] at hs; linarith
  have hsnonneg := (hbounds s hspos).2.1
  change p s = 0
  apply le_antisymm _ hsnonneg
  by_contra hnot
  have hps : 0 < p s := lt_of_not_ge hnot
  let C := 2 * H.scalar_constant + 1
  have hC : 0 < C := by dsimp only [C]; linarith [H.scalar_constant_pos]
  let z := C / p s + R + 1
  have hzR : R < z := by
    have hh := div_pos hC hps
    dsimp only [z]
    linarith only [hh]
  have hzpos : 0 < z := hR.trans hzR
  have hztail : s₀ < z := by dsimp only [R] at hzR; linarith
  have hsame : p z = p s := hconst hztail hstail
  obtain ⟨hzsquare, _, hzprod⟩ := hbounds z hzpos
  rw [hsame] at hzprod
  have hfC : f z ≤ C := by
    dsimp only [C]
    nlinarith only [hzsquare, sq_nonneg (f z - 1), H.scalar_constant_pos]
  have hmul : C < z * p s := by
    dsimp only [z]
    rw [add_mul, add_mul, div_mul_cancel₀ C hps.ne', one_mul]
    nlinarith only [mul_pos hR hps, hps]
  exact (not_le_of_gt hmul) (hzprod.trans hfC)

end PoincareConjecture.M35.Uniqueness
