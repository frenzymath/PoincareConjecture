import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.NormalModel













set_option autoImplicit false

open Set Metric

namespace Poincare.Riemannian.Soul

theorem span_ball_preimage_eq_of_radial_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} (e : E → M) {S : Set M} {R : ℝ}
    (hradial : ∀ v ∈ ball 0 R, e v ∈ S →
      ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ S)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    Submodule.span ℝ (ball 0 r ∩ e ⁻¹' S) =
      Submodule.span ℝ (ball 0 R ∩ e ⁻¹' S) := by
  apply le_antisymm (Submodule.span_mono (inter_subset_inter_left _ (ball_subset_ball hrR)))
  refine Submodule.span_le.mpr ?_
  intro v hv
  let t : ℝ := min 1 (r / (‖v‖ + 1)) / 2
  have hd : 0 < ‖v‖ + 1 := by positivity
  have ht : 0 < t := half_pos (lt_min zero_lt_one (div_pos hr hd))
  have ht1 : t ≤ 1 := by
    have := min_le_left (1 : ℝ) (r / (‖v‖ + 1))
    dsimp [t]
    linarith
  have htr : t < r / (‖v‖ + 1) :=
    (half_lt_self (lt_min zero_lt_one (div_pos hr hd))).trans_le (min_le_right _ _)
  have hsmall : ‖t • v‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    have := (lt_div_iff₀ hd).mp htr
    nlinarith
  apply (Submodule.smul_mem_iff _ ht.ne').mp
  exact Submodule.subset_span (R := ℝ) ⟨mem_ball_zero_iff.mpr hsmall,
    hradial v hv.1 hv.2 t ⟨ht.le, ht1⟩⟩

end Poincare.Riemannian.Soul
