import PoincareConjecture.Proofs.M04.ShiBarrierMaximum
import PoincareConjecture.Proofs.M09.LocalMinimumHessian
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

theorem halfLine_nonpositive_of_bounded
    {w : ℝ → ℝ → ℝ} {T K V M : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hcont : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ Ici 0))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (w t))
    (hbound : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, w t r ≤ M)
    (hinit : ∀ r ≥ 0, w 0 r ≤ 0)
    (htip : ∀ t ∈ Icc 0 T, w t 0 ≤ 0)
    (hPDE : ∀ t ∈ Ioc 0 T, ∀ r > 0, 0 < w t r →
      ∃ d : ℝ, HasDerivWithinAt (fun s => w s r) d (Icc 0 T) t ∧
        d ≤ deriv (deriv (w t)) r + V * |deriv (w t) r| + K * w t r) :
    ∀ t ∈ Icc 0 T, ∀ r ≥ 0, w t r ≤ 0 := by
  let L := K + V + 2
  have hL : 0 ≤ L := by dsimp only [L]; linarith
  have hε (epsilon : ℝ) (hepsilon : 0 < epsilon)
      (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) (hx : 0 ≤ x) :
      w t x ≤ epsilon * Real.exp (L * t) * (1 + x ^ 2) := by
    let B := x + |M| / epsilon + 2
    have hdiv : 0 ≤ |M| / epsilon := div_nonneg (abs_nonneg _) hepsilon.le
    have hB : 1 ≤ B := by dsimp only [B]; linarith only [hx, hdiv]
    have hxB : x ≤ B := by dsimp only [B]; linarith only [hdiv]
    have hfar : M ≤ epsilon * (1 + B ^ 2) := by
      have hBm : |M| / epsilon ≤ B := by dsimp only [B]; linarith
      have hprod := (div_le_iff₀ hepsilon).mp hBm
      have hsq : B ≤ 1 + B ^ 2 := by nlinarith only [sq_nonneg (B - 1)]
      have hmul := mul_le_mul_of_nonneg_left hsq hepsilon.le
      nlinarith only [hprod, hmul, le_abs_self M]
    let q : ℝ → ℝ → ℝ := fun s r => epsilon * Real.exp (L * s) * (1 + r ^ 2)
    let f : ℝ → ℝ → ℝ := fun s r => q s r - w s r
    have hqpos (s r : ℝ) : 0 < q s r := by dsimp only [q]; positivity
    have hqtime (s r : ℝ) : HasDerivAt (fun a => q a r) (L * q s r) s := by
      convert! (((hasDerivAt_id s).const_mul L).exp.const_mul epsilon).mul_const
        (1 + r ^ 2) using 1
      simp only [q, id_eq, mul_one]
      ring
    have hqr (s r : ℝ) : HasDerivAt (q s) (2 * epsilon * Real.exp (L * s) * r) r := by
      convert! (((hasDerivAt_id r).pow 2).const_add 1).const_mul
        (epsilon * Real.exp (L * s)) using 1
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    have hqrr (s r : ℝ) : HasDerivAt (deriv (q s))
        (2 * epsilon * Real.exp (L * s)) r := by
      have heq : deriv (q s) = fun z => 2 * epsilon * Real.exp (L * s) * z :=
        funext (fun z => (hqr s z).deriv)
      rw [heq]
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id r).const_mul (2 * epsilon * Real.exp (L * s))
    have hfcont : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ Icc 0 B) := by
      have hqc : Continuous (Function.uncurry q) := by dsimp only [q]; fun_prop
      exact hqc.continuousOn.sub (hcont.mono (prod_mono Subset.rfl Icc_subset_Ici_self))
    have hfinit (r : ℝ) (hr : r ∈ Icc 0 B) : 0 ≤ f 0 r :=
      sub_nonneg.mpr ((hinit r hr.1).trans (hqpos 0 r).le)
    have hfboundary (s : ℝ) (hs' : s ∈ Icc 0 T)
        (r : ℝ) (hr : r ∈ Icc 0 B \ interior (Icc 0 B)) : 0 ≤ f s r := by
      rw [interior_Icc] at hr
      have hend : r = 0 ∨ r = B := by
        by_cases hzero : r = 0
        · exact Or.inl hzero
        · exact Or.inr (le_antisymm hr.1.2
            (le_of_not_gt (fun hlt => hr.2 ⟨lt_of_le_of_ne hr.1.1 (Ne.symm hzero), hlt⟩)))
      rcases hend with rfl | rfl
      · exact sub_nonneg.mpr ((htip s hs').trans (hqpos s 0).le)
      · have he : 1 ≤ Real.exp (L * s) :=
          Real.one_le_exp_iff.mpr (mul_nonneg hL hs'.1)
        have hmul := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he hepsilon.le) (show 0 ≤ 1 + B ^ 2 by positivity)
        dsimp only [f, q]
        have hw := hbound s hs' B (by linarith only [hB])
        nlinarith only [hw, hfar, hmul]
    have hsupport (s : ℝ) (hs' : s ∈ Ioc 0 T) (r : ℝ)
        (hr : r ∈ interior (Icc 0 B)) (hmin : ∀ z ∈ Icc 0 B, f s r ≤ f s z)
        (hneg : f s r < 0) (delta : ℝ) (hdelta : 0 < delta) :
        ∃ ψ : ℝ → ℝ, ∃ d : ℝ, ψ s = f s r ∧
          (∀ᶠ a in 𝓝[Icc 0 s] s, f a r ≤ ψ a) ∧
          HasDerivWithinAt ψ d (Icc 0 s) s ∧ -(-K) * f s r - delta ≤ d := by
      have hscc : s ∈ Icc 0 T := ⟨hs'.1.le, hs'.2⟩
      have hrp : 0 < r := by rw [interior_Icc] at hr; exact hr.1
      have hlocal : IsLocalMin (f s) r := by
        filter_upwards [isOpen_interior.mem_nhds hr] with z hz
        exact hmin z (interior_subset hz)
      have hwpos : 0 < w s r := by
        have hqp := hqpos s r
        dsimp only [f] at hneg
        linarith
      have hws := hs s hscc
      have hwfirst (z : ℝ) : deriv (fun y => q s y - w s y) z =
          2 * epsilon * Real.exp (L * s) * z - deriv (w s) z :=
        ((hqr s z).sub ((hws.differentiable (by simp) z).hasDerivAt)).deriv
      have hfirst : deriv (w s) r = 2 * epsilon * Real.exp (L * s) * r := by
        have hz := hlocal.deriv_eq_zero
        change deriv (fun z => q s z - w s z) r = 0 at hz
        rw [hwfirst r] at hz
        linarith only [hz]
      have hfderiv : deriv (f s) = fun z => deriv (q s) z - deriv (w s) z := by
        funext z
        change deriv (fun y => q s y - w s y) z = _
        rw [hwfirst z, (hqr s z).deriv]
      have hwderiv := ((contDiff_infty_iff_deriv.mp hws).2.differentiable (by simp) r).hasDerivAt
      have hfsecond : deriv (fun z => deriv (q s) z - deriv (w s) z) r =
          2 * epsilon * Real.exp (L * s) - deriv (deriv (w s)) r :=
        ((hqrr s r).sub hwderiv).deriv
      have hsecond : deriv (deriv (w s)) r ≤ 2 * epsilon * Real.exp (L * s) := by
        have hz := PoincareConjecture.Proofs.M09.localMin_secondDeriv_nonneg (f s) r
          ((hqr s r).continuousAt.sub hws.continuous.continuousAt) hlocal
        rw [hfderiv, hfsecond] at hz
        linarith only [hz]
      obtain ⟨d, hd, hdb⟩ := hPDE s hs' r hrp hwpos
      have habs : |deriv (w s) r| = 2 * epsilon * Real.exp (L * s) * r := by
        rw [hfirst, abs_of_pos (by positivity)]
      rw [habs] at hdb
      have hpoly : 0 ≤ epsilon * Real.exp (L * s) *
          (2 * r ^ 2 + V * (r - 1) ^ 2) := by positivity
      refine ⟨fun a => f a r, L * q s r - d, rfl,
        Eventually.of_forall (fun _ => le_rfl),
        ((hqtime s r).hasDerivWithinAt.sub hd).mono (Icc_subset_Icc le_rfl hs'.2), ?_⟩
      dsimp only [f, q, L]
      dsimp only [L] at hdb hsecond hpoly
      nlinarith only [hdb, hsecond, hpoly, hdelta]
    have hcomparison := M04.compact_subset_min_velocity_nonnegative_of_upper_support
      (C := Icc 0 B) isCompact_Icc hT f hfinit hfboundary hfcont hsupport t ht x ⟨hx, hxB⟩
    exact sub_nonneg.mp hcomparison
  intro t ht x hx
  by_contra hbad
  have hw : 0 < w t x := lt_of_not_ge hbad
  let epsilon := w t x / (2 * (Real.exp (L * t) * (1 + x ^ 2)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hb := hε epsilon hepsilon t ht x hx
  have heq : epsilon * Real.exp (L * t) * (1 + x ^ 2) = w t x / 2 := by
    dsimp only [epsilon]
    field_simp [Real.exp_ne_zero, show 1 + x ^ 2 ≠ 0 by positivity]
  rw [heq] at hb
  linarith

end PoincareConjecture.M35.RadialGauge
