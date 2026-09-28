import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.DistinctPowers

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

theorem loopPowerThreshold_orbit_displacement {s ell : ℝ}
    (hs : 0 < s) (hell : 0 ≤ ell) (N : ℕ)
    (hshort : ell ≤ loopPowerThreshold s N) :
    2 * ((N : ℝ) + 1) * (2 * (N : ℝ) * ell) ≤
      (loopOrbitRadius s N / 2) / 16 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hfour : (2 : ℝ) ^ N ≤ (4 : ℝ) ^ N := by gcongr; norm_num
  have hp4 : 2 * (N : ℝ) * ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 4 := by
    nlinarith [sq_nonneg (N : ℝ), sq_nonneg ((N : ℝ) ^ 2),
      mul_nonneg hN (sq_nonneg (N : ℝ))]
  have hden : 0 < 1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by positivity
  have hcap : ell * (1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N) ≤ s :=
    (le_div_iff₀ hden).mp hshort
  have hcoeff : 2048 * (2 : ℝ) ^ N * (N : ℝ) * ((N : ℝ) + 1) ≤
      1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by
    calc
      _ = 1024 * (2 * (N : ℝ) * ((N : ℝ) + 1)) * (2 : ℝ) ^ N := by ring
      _ ≤ _ := by gcongr
  have hbig : 2048 * (2 : ℝ) ^ N * (N : ℝ) * ((N : ℝ) + 1) * ell ≤ s := by
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hell]
  have hscale : 512 * (2 : ℝ) ^ N * ((loopOrbitRadius s N / 2) / 16) = s := by
    unfold loopOrbitRadius
    field_simp
    norm_num
  have hscale_pos : 0 < 512 * (2 : ℝ) ^ N := by positivity
  apply (mul_le_mul_iff_right₀ hscale_pos).mp
  rw [hscale]
  nlinarith [hbig]

theorem loopPowerThreshold_orbit_energy {s ell : ℝ}
    (hs : 0 < s) (hell : 0 ≤ ell) (N : ℕ)
    (hshort : ell ≤ loopPowerThreshold s N) :
    2 * (N : ℝ) * ell < (loopOrbitRadius s N / 2) / 16 ∧
    (N : ℝ) * (2 * (N : ℝ) * ell) ^ 2 < ((loopOrbitRadius s N / 2) / 16) ^ 2 := by
  let delta := 2 * (N : ℝ) * ell
  let beta := (loopOrbitRadius s N / 2) / 16
  have hd : 0 ≤ delta := by dsimp [delta]; positivity
  have hb : 0 < beta := by dsimp [beta]; exact div_pos (div_pos (loopOrbitRadius_pos hs N) (by norm_num)) (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbound : 2 * ((N : ℝ) + 1) * delta ≤ beta :=
    loopPowerThreshold_orbit_displacement hs hell N hshort
  have hNb : (N : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]
  have hsq : (((N : ℝ) + 1) * delta) ^ 2 ≤ (beta / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  change delta < beta ∧ (N : ℝ) * delta ^ 2 < beta ^ 2
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hNb (sq_nonneg delta), sq_pos_of_pos hb]

theorem loopPowerThreshold_quarter_margin {s ell : ℝ}
    (hs : 0 < s) (hell : 0 ≤ ell) (N : ℕ)
    (hshort : ell ≤ loopPowerThreshold s N) :
    (2 : ℝ) ^ N * (loopOrbitRadius s N + ell) < s / 4 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp4 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hfour : (2 : ℝ) ^ N ≤ (4 : ℝ) ^ N := by gcongr; norm_num
  have hden : 0 < 1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by positivity
  have hcap : ell * (1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N) ≤ s :=
    (le_div_iff₀ hden).mp hshort
  have hcoeff : 1024 * (2 : ℝ) ^ N ≤
      1024 * ((N : ℝ) + 1) ^ 4 * (4 : ℝ) ^ N := by
    calc
      _ = 1024 * 1 * (2 : ℝ) ^ N := by ring
      _ ≤ _ := by gcongr
  have hbig : 1024 * (2 : ℝ) ^ N * ell ≤ s := by
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hell]
  have hscale : (2 : ℝ) ^ N * loopOrbitRadius s N = s / 16 := by
    unfold loopOrbitRadius
    field_simp
  rw [mul_add, hscale]
  nlinarith

theorem loopOrbitRadius_le_quarter {s : ℝ} (hs : 0 < s) (N : ℕ) :
    loopOrbitRadius s N ≤ s / 4 := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have hpos : 0 < (2 : ℝ) ^ N := by positivity
  unfold loopOrbitRadius
  apply (div_le_iff₀ (by positivity : 0 < 16 * (2 : ℝ) ^ N)).mpr
  nlinarith

theorem deck_motion_iterates_mem_quarter_ball
    {n : ℕ} {M : Type*} {f : EuclideanSpace ℝ (Fin n) → M} {s : ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContDiffOn ℝ ∞ d {x | ‖v‖ + 2 * ‖x‖ < s})
    (hdproj : EqOn (f ∘ d) f {x | ‖v‖ + 2 * ‖x‖ < s})
    (hdbound : ∀ x ∈ {x | ‖v‖ + 2 * ‖x‖ < s}, ‖d x - v‖ ≤ 2 * ‖x‖)
    (hs : 0 < s) (N : ℕ) (hshort : ‖v‖ ≤ loopPowerThreshold s N)
    (i : ℕ) (hi : i ≤ N) :
    MapsTo (d^[i]) (Metric.ball 0 (loopOrbitRadius s N / 2)) (Metric.ball 0 (s / 4)) := by
  have ha := loopOrbitRadius_pos hs N
  have hmargin := (loopPowerThreshold_margins hs (norm_nonneg v) N hshort).2
  have hcontrol := (deck_motion_iterates_controlled hd hdproj hdbound N hmargin i hi).2.2.2
  have hquarter := loopPowerThreshold_quarter_margin hs (norm_nonneg v) N hshort
  intro x hx
  have hxnorm : ‖x‖ < loopOrbitRadius s N / 2 := by simpa using hx
  have hxlarge : x ∈ Metric.ball 0 (loopOrbitRadius s N) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hbound := hcontrol x hxlarge
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi
  have hmul := mul_le_mul_of_nonneg_right hpow (add_nonneg (norm_nonneg x) (norm_nonneg v))
  have hmul' := mul_le_mul_of_nonneg_left
    (show ‖x‖ ≤ loopOrbitRadius s N by linarith) (by positivity : 0 ≤ (2 : ℝ) ^ N)
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg v]

end PoincareConjecture
