import PoincareConjecture.Proofs.M35.CapGeometry.InitialNeckScalar

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

theorem initial_cylinder_center_normalization_tendsto
    {theta : ℝ} (htheta : theta < 1) (delta t : ℕ → ℝ)
    (g : ℕ → RiemannianMetric 3 StandardCapSpace) (D : ∀ k, LeviCivitaData (g k))
    (x : ℕ → StandardCapSpace) (N : ∀ k, StandardCylinderPatch (delta k)⁻¹ (x k))
    (hd : ∀ k, 0 < delta k) (ht : ∀ k, t k ∈ Icc 0 theta)
    (hclose : ∀ k, RoundCylinderClose (delta k) (t k)
      (roundCylinderPullback (g k) (N k).coordinate))
    (hdlim : Tendsto delta atTop (𝓝 0)) :
    Tendsto (fun k => (1 - t k) * (D k).scalarCurvature (x k)) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro eta heta
  obtain ⟨d, hdpos, hcontrol⟩ := exists_initial_cylinder_scalar_control htheta heta
  obtain ⟨n, hn⟩ := eventually_atTop.mp
    (hdlim.eventually (eventually_le_nhds hdpos))
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨q, hq⟩ := (N k).center_sphere
  have h := hcontrol (delta k) (hd k) (hn k hk) (t k) (ht k)
    (g k) (D k) (x k) (N k) q (hclose k)
  simpa only [Real.dist_eq, hq] using h

theorem initial_cylinder_center_scalar_tendsto
    {theta : ℝ} (htheta : theta < 1) (delta t : ℕ → ℝ)
    (g : ℕ → RiemannianMetric 3 StandardCapSpace) (D : ∀ k, LeviCivitaData (g k))
    (x : ℕ → StandardCapSpace) (N : ∀ k, StandardCylinderPatch (delta k)⁻¹ (x k))
    (hd : ∀ k, 0 < delta k) (ht : ∀ k, t k ∈ Icc 0 theta)
    (hclose : ∀ k, RoundCylinderClose (delta k) (t k)
      (roundCylinderPullback (g k) (N k).coordinate))
    (hdlim : Tendsto delta atTop (𝓝 0)) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (htlim : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun k => (D k).scalarCurvature (x k)) atTop (𝓝 (1 / (1 - t₀))) := by
  have hnormal := initial_cylinder_center_normalization_tendsto htheta delta t g D x N
    hd ht hclose hdlim
  have hdiv := hnormal.div ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim)
    (sub_pos.mpr ht₀).ne'
  apply hdiv.congr'
  apply Eventually.of_forall
  intro k
  exact mul_div_cancel_left₀ ((D k).scalarCurvature (x k))
    (sub_pos.mpr ((ht k).2.trans_lt htheta)).ne'

theorem initial_affine_clock {theta t Q u : ℝ} (ht : t ∈ Icc 0 theta) (hQ : 0 < Q)
    (hu : u ∈ Icc (-t * Q) 0) :
    t + u / Q ∈ Icc 0 theta ∧
      Q * (1 - (t + u / Q)) - (1 - u) = (1 - t) * Q - 1 := by
  have hlo : -t ≤ u / Q := (le_div_iff₀ hQ).mpr (by nlinarith only [hu.1])
  have hhi : u / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu.2 hQ.le
  refine ⟨⟨by linarith only [hlo], by linarith only [hhi, ht.2]⟩, ?_⟩
  field_simp [hQ.ne']
  ring

end PoincareConjecture.M35
