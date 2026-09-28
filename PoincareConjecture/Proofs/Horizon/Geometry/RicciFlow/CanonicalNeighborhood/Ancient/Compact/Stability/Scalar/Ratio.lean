import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}


theorem scalar_uniform_lower_bound (A : CapCertificate g) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ A.carrier, a ≤ A.connection.scalarCurvature x := by
  obtain ⟨p, hp⟩ := A.core_nonempty
  have hp' := A.core_subset_carrier hp
  have hpos := A.scalar_pos p hp'
  refine ⟨A.connection.scalarCurvature p / A.cap_constant,
    div_pos hpos A.cap_constant_pos, fun x hx => ?_⟩
  apply (div_le_iff₀ A.cap_constant_pos).mpr
  simpa only [mul_comm] using (A.scalar_lt_constant_mul hx hp').le


theorem eventually_scalar_pos_and_ratio (A : CapCertificate g)
    {f : ℕ → M → ℝ}
    (hconv : TendstoUniformlyOn f A.connection.scalarCurvature atTop A.carrier) :
    ∀ᶠ k in atTop,
      (∀ x ∈ A.carrier, 0 < f k x) ∧
      ∃ b : ℝ, b < A.cap_constant ∧
        ∀ x ∈ A.carrier, ∀ y ∈ A.carrier, f k y ≤ b * f k x := by
  obtain ⟨a, ha, hlower⟩ := A.scalar_uniform_lower_bound
  obtain ⟨b, hb, hratio⟩ := A.scalar_ratio
  obtain ⟨p, hp⟩ := A.core_nonempty
  have hp' := A.core_subset_carrier hp
  have hb_one : 1 ≤ b := by
    have h := hratio p hp' p hp'
    have hpos := A.scalar_pos p hp'
    nlinarith
  have hC : 0 < A.cap_constant := A.cap_constant_pos
  let B := (b + A.cap_constant) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBC : B < A.cap_constant := by dsimp [B]; linarith
  let δ := min (a / 2) (a * (A.cap_constant - b) / (4 * (A.cap_constant + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ ≤ a / 2 := min_le_left _ _
  have hδC : 4 * (A.cap_constant + 1) * δ ≤ a * (A.cap_constant - b) := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (A.cap_constant + 1))).mp
      (show δ ≤ a * (A.cap_constant - b) / (4 * (A.cap_constant + 1)) from
        min_le_right _ _)
    nlinarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with k hk
  have hclose (x : M) (hx : x ∈ A.carrier) :
      |f k x - A.connection.scalarCurvature x| < δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using hk x hx
  refine ⟨?_, B, hBC, ?_⟩
  · intro x hx
    have h := (abs_lt.mp (hclose x hx)).1
    have hl := hlower x hx
    linarith
  · intro x hx y hy
    have hfx := (abs_lt.mp (hclose x hx)).1
    have hfy := (abs_lt.mp (hclose y hy)).2
    have hr := hratio x hx y hy
    have hl := hlower x hx
    have hmargin := mul_nonneg (sub_nonneg.mpr hb.le) (sub_nonneg.mpr hl)
    have hBδ := mul_le_mul_of_nonneg_right hBC.le hδ.le
    have hBx := mul_nonneg hB.le (show 0 ≤ f k x -
      A.connection.scalarCurvature x + δ by linarith)
    dsimp only [B] at hBδ hBx ⊢
    nlinarith

end PoincareConjecture.CapCertificate
