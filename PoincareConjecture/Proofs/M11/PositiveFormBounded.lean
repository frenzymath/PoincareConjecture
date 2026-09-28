import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false

open Set Metric Bornology

namespace PoincareConjecture.Proofs.M11

theorem positiveForm_isVonNBounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v, v ≠ 0 → 0 < g v v) :
    IsVonNBounded ℝ {v : E | g v v < 1} := by
  apply NormedSpace.isVonNBounded_of_isBounded
  by_cases hsub : Subsingleton E
  · let := hsub
    exact (isBounded_singleton (x := (0 : E))).subset (fun v _ ↦ Subsingleton.elim v 0)
  let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
  have hcont : Continuous (fun v ↦ g v v) := g.continuous₂.comp (continuous_id.prodMk continuous_id)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  have hu0 : u ≠ 0 := ne_of_mem_sphere hu one_ne_zero
  have hδ := hpos u hu0
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max 1 (1 / g u u), ?_⟩
  intro v hv
  change g v v < 1 at hv
  by_cases hv0 : v = 0
  · simp only [hv0, norm_zero]
    exact (by positivity : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hunit : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
    simp [norm_smul, norm_inv, hnorm]
  have hbound := mul_le_mul_of_nonneg_left (hmin hunit) (sq_nonneg ‖v‖)
  have hscale : ‖v‖ ^ 2 * g (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = g v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  rw [hscale] at hbound
  by_contra! hlarge
  have hlarge₁ : 1 < ‖v‖ := (le_max_left _ _).trans_lt hlarge
  have hlarge₂ : 1 < g u u * ‖v‖ := by
    have := (le_max_right 1 (1 / g u u)).trans_lt hlarge
    have := (div_lt_iff₀ hδ).mp this
    nlinarith
  have := mul_lt_mul_of_pos_right hlarge₂ (norm_pos_iff.mpr hv0)
  nlinarith

end PoincareConjecture.Proofs.M11
