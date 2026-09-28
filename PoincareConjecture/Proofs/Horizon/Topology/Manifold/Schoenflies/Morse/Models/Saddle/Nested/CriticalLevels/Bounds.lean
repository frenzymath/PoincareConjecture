import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Uniqueness



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem critical_norm {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) :
    ((p : E3) 0)^2 + ((p : E3) 2)^2 = 1 := by
  have hy := (critical_point_coordinates hp).1
  have hn := EuclideanSpace.norm_sq_eq (p : E3)
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy] at hn
  exact hn.symm

private theorem critical_height {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) :
    height p = 1 + (p : E3) 2 - ((p : E3) 2)^2 + (3 / 10) * (p : E3) 0 := by
  rw [height_apply, (critical_point_coordinates hp).1]
  nlinarith [critical_norm hp]

theorem criticalPolynomial_pos_above_saddle {z : Real}
    (hz : z ∈ Icc (5 / 8 : Real) (9 / 10)) : 0 < criticalPolynomial z := by
  let t := (40 / 11 : Real) * (z - 5 / 8)
  have ht : 0 ≤ t := by dsimp [t]; linarith [hz.1]
  have htc : 0 ≤ 1 - t := by dsimp [t]; linarith [hz.2]
  have he : criticalPolynomial z = (3 / 1024 : Real) +
      (737 / 6400) * t * (1 - t)^3 + (135597 / 320000) * t^2 * (1 - t)^2 +
      (60357 / 160000) * t^3 * (1 - t) + (29293 / 640000) * t^4 := by
    dsimp [criticalPolynomial, t]
    ring
  rw [he]
  positivity

theorem criticalPolynomial_neg_below_saddle {z : Real}
    (hz : z ∈ Icc (1 / 2 : Real) (3 / 5)) : criticalPolynomial z < 0 := by
  let t := (10 : Real) * (z - 1 / 2)
  have ht : 0 ≤ t := by dsimp [t]; linarith [hz.1]
  have htc : 0 ≤ 1 - t := by dsimp [t]; linarith [hz.2]
  have he : criticalPolynomial z = -(17 / 2500 : Real) -
      (157 / 10000) * (1 - t)^4 - (359 / 5000) * t * (1 - t)^3 -
      (921 / 10000) * t^2 * (1 - t)^2 - (89 / 2500) * t^3 * (1 - t) := by
    dsimp [criticalPolynomial, t]
    ring
  rw [he]
  have h₀ : 0 ≤ (157 / 10000 : Real) * (1 - t)^4 := by positivity
  have h₁ : 0 ≤ (359 / 5000 : Real) * t * (1 - t)^3 := by positivity
  have h₂ : 0 ≤ (921 / 10000 : Real) * t^2 * (1 - t)^2 := by positivity
  have h₃ : 0 ≤ (89 / 2500 : Real) * t^3 * (1 - t) := by positivity
  linarith

theorem critical_height_lt_one_of_latitude_nonpos {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) (hz : (p : E3) 2 ≤ 0) :
    height p < 1 := by
  have hc := (critical_point_coordinates hp).2
  have hn := critical_norm hp
  have hx : (p : E3) 0 ≤ 0 := by
    by_contra hx
    have hx' : 0 < (p : E3) 0 := lt_of_not_ge hx
    have hm : (p : E3) 0 * (2 * (p : E3) 2 - 1) < 0 :=
      mul_neg_of_pos_of_neg hx' (by linarith)
    nlinarith
  have hz' : (p : E3) 2 < 0 := by
    by_contra hz'
    have he : (p : E3) 2 = 0 := le_antisymm hz (le_of_not_gt hz')
    rw [he] at hc hn
    norm_num at hc
    nlinarith
  rw [critical_height hp]
  nlinarith [sq_nonneg ((p : E3) 2)]

theorem critical_height_gt_thirteen_tenths_of_small_positive_latitude {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hz : 0 < (p : E3) 2) (hz' : (p : E3) 2 < 1 / 2) :
    (13 / 10 : Real) < height p := by
  have hc := (critical_point_coordinates hp).2
  have hn := critical_norm hp
  have hx : 0 < (p : E3) 0 := by
    by_contra hx
    have hmul : 0 ≤ (p : E3) 0 * (2 * (p : E3) 2 - 1) :=
      mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hx) (by linarith)
    nlinarith
  have hzz : 0 < (p : E3) 2 * (1 - (p : E3) 2) := mul_pos hz (by linarith)
  have hxb : 1 - (p : E3) 2 < (p : E3) 0 := by nlinarith
  have hzz' : 0 < (p : E3) 2 * (7 / 10 - (p : E3) 2) := mul_pos hz (by linarith)
  rw [critical_height hp]
  nlinarith

theorem critical_height_lt_one_of_large_latitude {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) (hz : (9 / 10 : Real) ≤ (p : E3) 2) :
    height p < 1 := by
  have hc := (critical_point_coordinates hp).2
  have hn := critical_norm hp
  have hzu : (p : E3) 2 ≤ 1 := by nlinarith [sq_nonneg ((p : E3) 0)]
  have hprod : 0 ≤ ((p : E3) 2 - 9 / 10) * (2 * (p : E3) 2 - 6 / 5) :=
    mul_nonneg (by linarith) (by linarith)
  have hfactor : (1 - (p : E3) 2) * (2 * (p : E3) 2 - 1) - 9 / 100 < 0 := by
    nlinarith
  have hnegative : (p : E3) 2 *
      ((1 - (p : E3) 2) * (2 * (p : E3) 2 - 1) - 9 / 100) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hfactor
  rw [critical_height hp]
  by_contra hh
  have hnonneg : 0 ≤
      ((p : E3) 2 - ((p : E3) 2)^2 + (3 / 10) * (p : E3) 0) *
        (2 * (p : E3) 2 - 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith


theorem critical_latitude_in_saddle_interval_of_height_band {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hh : height p ∈ Icc (1 : Real) (13 / 10)) :
    (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) := by
  have hzero := critical_polynomial_eq_zero hp
  have hz0 : 0 < (p : E3) 2 := by
    by_contra hz
    have := critical_height_lt_one_of_latitude_nonpos hp (le_of_not_gt hz)
    linarith [hh.1]
  have hzh : (1 / 2 : Real) ≤ (p : E3) 2 := by
    by_contra hz
    have := critical_height_gt_thirteen_tenths_of_small_positive_latitude hp hz0 (lt_of_not_ge hz)
    linarith [hh.2]
  have hzl : (3 / 5 : Real) < (p : E3) 2 := by
    by_contra hz
    have := criticalPolynomial_neg_below_saddle ⟨hzh, le_of_not_gt hz⟩
    linarith
  have hzu : (p : E3) 2 < (9 / 10 : Real) := by
    by_contra hz
    have := critical_height_lt_one_of_large_latitude hp (le_of_not_gt hz)
    linarith [hh.1]
  refine ⟨hzl, ?_⟩
  by_contra hz
  have := criticalPolynomial_pos_above_saddle ⟨le_of_not_gt hz, hzu.le⟩
  linarith

end Poincare.Manifold.Schoenflies.Saddle.Nested
