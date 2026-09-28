import PoincareConjecture.Proofs.M35.RadialGauge.PicardDerivativeEnd
import PoincareConjecture.Proofs.M35.RadialGauge.PicardC3Limit

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open Set Filter
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {A F : Type*} [NormedAddCommGroup F]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem weighted_geometric_limit_vanishes_uniformly
    {f : ℕ → A → V → F} {u : A → V → F} {C : ℝ}
    (htail : ∀ k a x, (1 + ‖x‖) * ‖f k a x - u a x‖ ≤ C * (1 / 2 : ℝ) ^ k)
    (hend : ∀ k, ∀ e > 0, ∃ R : ℝ, ∀ a x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖f k a x‖ < e) :
    ∀ e > 0, ∃ R : ℝ, ∀ a x, R ≤ ‖x‖ → (1 + ‖x‖) * ‖u a x‖ < e := by
  intro e he
  have hz : Tendsto (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
  obtain ⟨k, hk⟩ := ((tendsto_order.mp hz).2 (e / 2) (by linarith only [he])).exists
  obtain ⟨R, hR⟩ := hend k (e / 2) (by linarith only [he])
  refine ⟨R, fun a x hx => ?_⟩
  have hn : ‖u a x‖ ≤ ‖f k a x - u a x‖ + ‖f k a x‖ := by
    calc
      _ = ‖(u a x - f k a x) + f k a x‖ := by rw [sub_add_cancel]
      _ ≤ ‖u a x - f k a x‖ + ‖f k a x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev (u a x) (f k a x)]
  have hw := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1 + ‖x‖ by positivity)
  nlinarith only [hw, htail k a x, hR a x hx, hk]

noncomputable local instance m35PicardLimitEndLocal1 :
    NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardLimitEndLocal2 :
    NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem gaugePicard_limit_derivatives_weighted_vanish_uniformly
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T C1 C2 : ℝ}
    (htail1 : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x - fderiv ℝ (u t) x‖ ≤ C1 * (1 / 2 : ℝ) ^ k)
    (htail2 : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x -
        fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C2 * (1 / 2 : ℝ) ^ k)
    (hend : ∀ k, ∀ e > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x‖ < e ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ < e) :
    ∀ e > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ < e ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ < e := by
  have hfirst := weighted_geometric_limit_vanishes_uniformly
    (f := fun k (t : Icc 0 T) => fderiv ℝ (gaugePicard b G k t.1))
    (u := fun t : Icc 0 T => fderiv ℝ (u t.1))
    (fun k t => htail1 k t.1 t.2)
    (fun k e he => by
      obtain ⟨R, hR⟩ := hend k e he
      exact ⟨R, fun t x hx => (hR t.1 t.2 x hx).1⟩)
  have hsecond := weighted_geometric_limit_vanishes_uniformly
    (f := fun k (t : Icc 0 T) => fderiv ℝ (fderiv ℝ (gaugePicard b G k t.1)))
    (u := fun t : Icc 0 T => fderiv ℝ (fderiv ℝ (u t.1)))
    (fun k t => htail2 k t.1 t.2)
    (fun k e he => by
      obtain ⟨R, hR⟩ := hend k e he
      exact ⟨R, fun t x hx => (hR t.1 t.2 x hx).2⟩)
  intro e he
  obtain ⟨R1, hR1⟩ := hfirst e he
  obtain ⟨R2, hR2⟩ := hsecond e he
  exact ⟨max R1 R2, fun t ht x hx =>
    ⟨hR1 ⟨t, ht⟩ x ((le_max_left _ _).trans hx), hR2 ⟨t, ht⟩ x ((le_max_right _ _).trans hx)⟩⟩

end PoincareConjecture.M35.RadialGauge
