import PoincareConjecture.Proofs.M76.Mathlib.AlexanderIsotopy









set_option autoImplicit false

open Set
open scoped Topology

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E]



theorem norm_apply_le_of_fixed_outside (e : E ≃ₜ E) {R : ℝ}
    (he : ∀ x, R ≤ ‖x‖ → e x = x) {x : E} (hx : ‖x‖ ≤ R) : ‖e x‖ ≤ R := by
  by_contra hn
  have hfix : e (e x) = e x := he _ (le_of_lt (lt_of_not_ge hn))
  have hex : e x = x := e.injective hfix
  exact hn (by simpa only [hex] using hx)



theorem norm_sub_le_of_fixed_outside (e : E ≃ₜ E) {R : ℝ} (hR : 0 ≤ R)
    (he : ∀ x, R ≤ ‖x‖ → e x = x) (x : E) : ‖e x - x‖ ≤ 2 * R := by
  by_cases hx : ‖x‖ ≤ R
  · calc
      ‖e x - x‖ ≤ ‖e x‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (e.norm_apply_le_of_fixed_outside he hx) hx
      _ = 2 * R := by ring
  · rw [he _ (le_of_lt (lt_of_not_ge hx)), sub_self, norm_zero]
    exact mul_nonneg (by norm_num) hR

variable [NormedSpace ℝ E]




theorem alexanderFamily_apply_of_fixed_outside (e : E ≃ₜ E) {R : ℝ}
    (he : ∀ x, R ≤ ‖x‖ → e x = x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {x : E} (hx : R ≤ ‖x‖) : e.alexanderFamily t x = x := by
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hscale : ‖x‖ ≤ ‖t⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    exact le_mul_of_one_le_left (norm_nonneg _) ((one_le_inv₀ htpos).mpr ht.2)
  rw [e.alexanderFamily_apply_of_ne_zero ht0, he _ (hx.trans hscale), smul_inv_smul₀ ht0]




noncomputable def alexanderHomotopy (e : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖e x - x‖ ≤ C) :
    ContinuousMap.HomotopyWith (ContinuousMap.id E) ⟨e, e.continuous⟩
      (fun f => IsHomeomorph f) where
  toFun p := e.alexanderFamily (p.1 : ℝ) p.2
  continuous_toFun := (e.continuous_alexanderFamily hC).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := by simp
  map_one_left x := by simp
  prop' t := (e.alexanderFamily (t : ℝ)).isHomeomorph



noncomputable def supportedAlexanderHomotopy (e : E ≃ₜ E) {R : ℝ} (hR : 0 ≤ R)
    (he : ∀ x, R ≤ ‖x‖ → e x = x) :
    ContinuousMap.HomotopyWith (ContinuousMap.id E) ⟨e, e.continuous⟩
      (fun f => IsHomeomorph f ∧ ∀ x, R ≤ ‖x‖ → f x = x) where
  toHomotopy := (e.alexanderHomotopy (e.norm_sub_le_of_fixed_outside hR he)).toHomotopy
  prop' t := ⟨(e.alexanderFamily (t : ℝ)).isHomeomorph,
    fun _ hx => e.alexanderFamily_apply_of_fixed_outside he t.property hx⟩

end Homeomorph
