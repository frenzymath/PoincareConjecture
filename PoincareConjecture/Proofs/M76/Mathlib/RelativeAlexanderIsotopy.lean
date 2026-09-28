import PoincareConjecture.Proofs.M76.Mathlib.SupportedAlexanderIsotopy
import Mathlib.Analysis.Convex.Star










set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem alexanderFamily_fixed_compl_starConvex (e : E ≃ₜ E) {S : Set E}
    (hS : StarConvex ℝ (0 : E) S) (he : ∀ x ∉ S, e x = x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : E} (hx : x ∉ S) :
    e.alexanderFamily t x = x := by
  by_cases ht0 : t = 0
  · simp [ht0]
  have hscaled : t⁻¹ • x ∉ S := by
    intro h
    have h' := hS.smul_mem h ht.1 ht.2
    rw [smul_inv_smul₀ ht0] at h'
    exact hx h'
  rw [e.alexanderFamily_apply_of_ne_zero ht0, he _ hscaled, smul_inv_smul₀ ht0]




theorem alexanderFamily_fixed_relative (e : E ≃ₜ E) {S : Set E}
    (hS : StarConvex ℝ (0 : E) S) (he : ∀ x ∉ S, e x = x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : E} (hx : x ∈ Sᶜ ∪ frontier S) :
    e.alexanderFamily t x = x := by
  have hfix : EqOn (e.alexanderFamily t) id Sᶜ :=
    fun _ hy => e.alexanderFamily_fixed_compl_starConvex hS he ht hy
  rcases hx with hx | hx
  · exact hfix hx
  · exact hfix.closure (e.alexanderFamily t).continuous continuous_id
      (frontier_eq_closure_inter_closure (s := S) ▸ hx).2




noncomputable def relativeSupportedAlexanderHomotopy (e : E ≃ₜ E)
    {R : ℝ} (hR : 0 ≤ R) (hball : ∀ x, R ≤ ‖x‖ → e x = x)
    {S : Set E} (hS : StarConvex ℝ (0 : E) S) (he : ∀ x ∉ S, e x = x) :
    ContinuousMap.HomotopyWith (ContinuousMap.id E) ⟨e, e.continuous⟩
      (fun f => IsHomeomorph f ∧ (∀ x, R ≤ ‖x‖ → f x = x) ∧
        ∀ x ∈ Sᶜ ∪ frontier S, f x = x) where
  toHomotopy := (e.supportedAlexanderHomotopy hR hball).toHomotopy
  prop' t := ⟨(e.alexanderFamily (t : ℝ)).isHomeomorph,
    fun _ hx => e.alexanderFamily_apply_of_fixed_outside hball t.property hx,
    fun _ hx => e.alexanderFamily_fixed_relative hS he t.property hx⟩

end Homeomorph
