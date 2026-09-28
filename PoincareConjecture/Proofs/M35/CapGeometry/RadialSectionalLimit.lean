import PoincareConjecture.Proofs.M35.CapGeometry.FarTipSlope

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem nonpos_tendsto_zero_of_nonneg_controlled_drop
    {f q : ℕ → ℝ}
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hq_nonpos : ∀ k, q k ≤ 0)
    (hdrop : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ k, q k ≤ -ε → δ ≤ f k)
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto q atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < -a := by linarith
    obtain ⟨δ, hδ, hδdrop⟩ := hdrop (-a) hε
    filter_upwards [hf.eventually (eventually_lt_nhds hδ)] with k hk
    by_contra hnot
    have hq : q k ≤ -(-a) := by linarith
    have hfloor := hδdrop k hq
    have hk0 := hf_nonneg k
    linarith
  · intro a ha
    filter_upwards [Eventually.of_forall hq_nonpos] with k hk
    linarith

theorem radialMixedCurvatureFactor_tendsto_zero_of_second
    {g : ℕ → RiemannianMetric 3 StandardCapSpace}
    {r : ℕ → ℝ} {ρ : ℝ}
    (hr : ∀ k, 0 < r k)
    (hsecond : Tendsto (fun k => axisWarpingSecond (g k) (r k))
      atTop (𝓝 0))
    (hradius : Tendsto (fun k => axisWarpingRadius (g k) (r k))
      atTop (𝓝 ρ))
    (hρ : 0 < ρ) :
    Tendsto (fun k => radialMixedCurvatureFactor (g k) (r k) /
      axisRadialCoefficient (g k) (r k)) atTop (𝓝 0) := by
  have heq : (fun k => radialMixedCurvatureFactor (g k) (r k) /
      axisRadialCoefficient (g k) (r k)) =
      (fun k => -axisWarpingSecond (g k) (r k) /
        axisWarpingRadius (g k) (r k)) := by
    funext k
    exact radialMixedCurvatureFactor_eq_warping (g k) (hr k)
  rw [heq]
  convert! hsecond.neg.div hradius (ne_of_gt hρ) using 1
  simp

theorem intrinsic_second_tendsto_zero_of_lipschitz
    {f q : ℝ → ℝ} {s : ℕ → ℝ} {L : ℝ}
    (hf_nonneg : ∀ u, 0 ≤ f u)
    (hderiv : ∀ u, HasDerivAt f (q u) u)
    (hq_nonpos : ∀ u, q u ≤ 0)
    (hqlip : ∀ u v, |q u - q v| ≤ L * |u - v|)
    (hL : 0 < L)
    (hfs : Tendsto (fun k => f (s k)) atTop (𝓝 0)) :
    Tendsto (fun k => q (s k)) atTop (𝓝 0) := by
  apply nonpos_tendsto_zero_of_nonneg_controlled_drop
    (f := fun k => f (s k)) (q := fun k => q (s k))
    (fun k => hf_nonneg (s k)) (fun k => hq_nonpos (s k))
    (fun ε hε => ?_) hfs
  refine ⟨ε ^ 2 / (4 * L), by positivity, ?_⟩
  intro k hk
  let t := s k + ε / (2 * L)
  have hst : s k ≤ t := by
    dsimp [t]
    exact le_add_of_nonneg_right (by positivity)
  have hqbound (u : ℝ) (hu : u ∈ Icc (s k) t) : q u ≤ -ε / 2 := by
    have hdist := hqlip u (s k)
    have hudiff : |u - s k| ≤ ε / (2 * L) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      have huupper : u ≤ s k + ε / (2 * L) := hu.2
      linarith only [huupper]
    have hmul : L * |u - s k| ≤ ε / 2 := by
      calc
        L * |u - s k| ≤ L * (ε / (2 * L)) :=
          mul_le_mul_of_nonneg_left hudiff hL.le
        _ = ε / 2 := by field_simp [hL.ne']
    have hqdiff : q u - q (s k) ≤ |q u - q (s k)| := le_abs_self _
    have hqk := hk
    linarith
  have hdec := (convex_Icc (s k) t).image_sub_le_mul_sub_of_deriv_le
    (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
    (fun u _ => (hderiv u).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hderiv u).deriv]
      exact hqbound u (interior_subset hu))
    (s k) ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have hcalc : (-ε / 2) * (t - s k) = -ε ^ 2 / (4 * L) := by
    dsimp [t]
    field_simp [hL.ne']
    ring
  rw [hcalc] at hdec
  have hdec' : f t - f (s k) ≤ -(ε ^ 2 / (4 * L)) := by
    simpa only [neg_div] using hdec
  have htpos := hf_nonneg t
  linarith only [hdec', htpos]

end PoincareConjecture.M35.Uniqueness
