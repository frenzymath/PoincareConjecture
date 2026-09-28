import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.DistanceChord
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false

open Set Filter Topology

namespace Poincare.Alexandrov

private theorem eventually_pos_of_hasDerivAt_pos
    {f : ℝ → ℝ} {a : ℝ} (hf : HasDerivAt f a 0) (ha : 0 < a) (h0 : f 0 = 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have hslope := hf.tendsto_slope_zero_right.eventually_const_lt ha
  filter_upwards [hslope, self_mem_nhdsWithin] with t ht htpos
  have hmul : 0 < t⁻¹ * f t := by simpa only [zero_add, h0, sub_zero, smul_eq_mul] using ht
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr htpos)).mp hmul

theorem CurvatureGEnegOne.exists_local_distance_ascent_of_comparisonAngle
    {X : Type*} [MetricSpace X] (hX : CurvatureGEnegOne X)
    {p y q : X} (hpy : p ≠ y) (hqy : q ≠ y)
    (γ : ℝ → X) (hγ0 : γ 0 = y) (hγ1 : γ 1 = q)
    (hγdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist y q)
    {c : ℝ} (hc : 0 ≤ c)
    (hangle : c < -Real.cos (comparisonAngle (dist y p) (dist y q) (dist p q))) :
    ∀ s : ℝ, 0 < s → ∃ z : X,
      dist y z < s ∧ c * dist y z < dist p z - dist p y := by
  let a := dist p y
  let ell := dist y q
  let d := dist p q
  have ha : 0 < a := dist_pos.mpr hpy
  have hell : 0 < ell := dist_pos.mpr hqy.symm
  have hsinha : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hsinhell : 0 < Real.sinh ell := Real.sinh_pos_iff.mpr hell
  have hden : 0 < Real.sinh a * Real.sinh ell := mul_pos hsinha hsinhell
  rw [dist_comm y p] at hangle
  change c < -Real.cos (comparisonAngle a ell d) at hangle
  have htriangle : |a - ell| ≤ d := by
    simpa only [a, ell, d, dist_comm q y] using abs_dist_sub_le p q y
  rw [cos_comparisonAngle ha hell dist_nonneg htriangle (dist_triangle p y q),
    ← neg_div, lt_div_iff₀ hden] at hangle
  have hderivpos : 0 < ell * (Real.cosh d - Real.cosh a * Real.cosh ell -
      c * Real.sinh a * Real.sinh ell) := by
    apply mul_pos hell
    nlinarith only [hangle]
  let F : ℝ → ℝ := fun t =>
    Real.cosh a * Real.sinh ((1 - t) * ell) + Real.cosh d * Real.sinh (t * ell) -
      Real.cosh (a + c * t * ell) * Real.sinh ell
  have hF0 : F 0 = 0 := by simp [F]
  have hFderiv : HasDerivAt F
      (ell * (Real.cosh d - Real.cosh a * Real.cosh ell -
        c * Real.sinh a * Real.sinh ell)) 0 := by
    have h1 := (((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const ell).sinh.const_mul
      (Real.cosh a)
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const ell).sinh.const_mul (Real.cosh d)
    have h3 := ((((hasDerivAt_id (0 : ℝ)).const_mul c).mul_const ell).const_add a).cosh.mul_const
      (Real.sinh ell)
    convert! (h1.add h2).sub h3 using 1
    simp only [id_eq, sub_zero, one_mul, neg_one_mul, zero_mul, mul_zero, Real.cosh_zero,
      mul_one, add_zero]
    ring
  have hFpos := eventually_pos_of_hasDerivAt_pos hFderiv hderivpos hF0
  intro s hs
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min 1 (s / ell) :=
    (eventually_lt_nhds (lt_min zero_lt_one (div_pos hs hell))).filter_mono
      nhdsWithin_le_nhds
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htF, ht0, htsmall⟩ :=
    (hFpos.and (hpositive.and hsmall)).exists
  have ht1 : t < 1 := lt_of_lt_of_le htsmall (min_le_left _ _)
  have hts : t * ell < s :=
    (lt_div_iff₀ hell).mp (lt_of_lt_of_le htsmall (min_le_right _ _))
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hyz : dist y (γ t) = t * ell := by
    have h := hγdist 0 ⟨le_rfl, zero_le_one⟩ t htI
    simpa only [hγ0, zero_sub, abs_neg, abs_of_pos ht0] using h
  have hzq : dist (γ t) q = (1 - t) * ell := by
    have h := hγdist t htI 1 ⟨zero_le_one, le_rfl⟩
    simpa only [hγ1, abs_of_neg (sub_neg.mpr ht1), neg_sub] using h
  have hyzpos : 0 < dist y (γ t) := by rw [hyz]; positivity
  have hzqpos : 0 < dist (γ t) q := by rw [hzq]; positivity
  have hbetween : dist y q = dist y (γ t) + dist (γ t) q := by
    rw [hyz, hzq]
    change ell = t * ell + (1 - t) * ell
    ring
  have hchord := hX.cosh_distance_chord_lower_bound (p := p) hyzpos hzqpos hbetween
  rw [hyz, hzq] at hchord
  have hcoshlt : Real.cosh (a + c * t * ell) < Real.cosh (dist p (γ t)) := by
    apply (mul_lt_mul_iff_left₀ hsinhell).mp
    dsimp [F] at htF
    nlinarith only [htF, hchord]
  have hincrement : a + c * t * ell < dist p (γ t) := by
    have h := Real.cosh_lt_cosh.mp hcoshlt
    simpa only [abs_of_nonneg (show 0 ≤ a + c * t * ell by positivity),
      abs_of_nonneg dist_nonneg] using h
  refine ⟨γ t, ?_, ?_⟩
  · rw [hyz]
    exact hts
  · rw [hyz]
    dsimp [a] at hincrement
    linarith

end Poincare.Alexandrov
