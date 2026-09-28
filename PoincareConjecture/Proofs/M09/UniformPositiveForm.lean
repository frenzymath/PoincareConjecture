import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

open scoped Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]

theorem exists_uniform_positiveForm_lower_bound
    (G : X → E →L[ℝ] E →L[ℝ] ℝ) (x0 : X) (hG : ContinuousAt G x0)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G x0 v v) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧
      ∀ x ∈ U, ∀ v : E, c * ‖v‖ ^ 2 ≤ G x v v := by
  classical
  let S := Metric.sphere (0 : E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hunit (v : E) (hv : v ≠ 0) : (‖v‖⁻¹ : ℝ) • v ∈ S := by
    simpa [S, Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hv
  rcases S.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, zero_lt_one, Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
    intro x _ v
    have hv : v = 0 := by
      by_contra hv
      have h := hunit v hv
      simpa only [hempty, Set.mem_empty_iff_false] using h
    simp only [hv, norm_zero, zero_pow two_ne_zero, mul_zero, map_zero, zero_apply, le_refl]
  · have heval : Continuous (fun v : E ↦ G x0 v v) :=
      (continuous_const.clm_apply continuous_id).clm_apply continuous_id
    obtain ⟨v0, hv0, hmin⟩ := hS.exists_isMinOn hne heval.continuousOn
    have hv0ne : v0 ≠ 0 := by
      have hn : ‖v0‖ = 1 := by simpa only [S, Metric.mem_sphere, dist_zero_right] using hv0
      intro hz
      simpa only [hz, norm_zero, zero_ne_one] using hn
    let c := G x0 v0 v0 / 2
    have hc : 0 < c := div_pos (hpos v0 hv0ne) zero_lt_two
    have hnear : ∀ᶠ x in 𝓝 x0, ∀ v ∈ S, c < G x v v := by
      apply hS.eventually_forall_of_forall_eventually
      intro v hv
      have hvalue : c < G x0 v v := by
        have hmin' : G x0 v0 v0 ≤ G x0 v v := hmin hv
        have hpos' := hpos v0 hv0ne
        dsimp only [c]
        linarith
      have hcont : ContinuousAt (fun z : X × E ↦ G z.1 z.2 z.2) (x0, v) :=
        ((hG.comp (continuousAt_fst (p := (x0, v)))).clm_apply
          continuousAt_snd).clm_apply continuousAt_snd
      exact hcont.eventually (isOpen_Ioi.mem_nhds hvalue)
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
    refine ⟨c, hc, U, hU, hxU, ?_⟩
    intro x hx v
    rcases eq_or_ne v 0 with rfl | hv
    · simp only [norm_zero, zero_pow two_ne_zero, mul_zero, map_zero, zero_apply, le_refl]
    · let u : E := (‖v‖⁻¹ : ℝ) • v
      have hu : u ∈ S := hunit v hv
      have hscale : ‖v‖ • u = v := by
        simp only [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
      calc
        c * ‖v‖ ^ 2 ≤ G x u u * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hUsub hx u hu).le (sq_nonneg _)
        _ = G x (‖v‖ • u) (‖v‖ • u) := by
          simp only [map_smul, smul_apply, smul_eq_mul]
          ring
        _ = G x v v := by rw [hscale]

theorem covector_sq_le_positiveForm
    (G : E →L[ℝ] E →L[ℝ] ℝ) (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D)
    (hG : ∀ v : E, c * ‖v‖ ^ 2 ≤ G v v)
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ D) (v : E) :
    (L v) ^ 2 ≤ (D ^ 2 / c) * G v v := by
  have hbound : |L v| ≤ D * ‖v‖ :=
    (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hsq : (L v) ^ 2 ≤ D ^ 2 * ‖v‖ ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD (norm_nonneg _))).mpr hbound
    simpa only [sq_abs, mul_pow] using h
  have hnorm : ‖v‖ ^ 2 ≤ G v v / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hG v)
  calc
    _ ≤ D ^ 2 * ‖v‖ ^ 2 := hsq
    _ ≤ D ^ 2 * (G v v / c) := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _ = _ := by ring

theorem bilinear_le_positiveForm
    (G : E →L[ℝ] E →L[ℝ] ℝ) (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D)
    (hG : ∀ v : E, c * ‖v‖ ^ 2 ≤ G v v)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : ‖H‖ ≤ D) (v : E) :
    H v v ≤ (D / c) * G v v := by
  have hnorm : ‖v‖ ^ 2 ≤ G v v / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hG v)
  calc
    H v v ≤ |H v v| := le_abs_self _
    _ ≤ ‖H v‖ * ‖v‖ := (H v).le_opNorm v
    _ ≤ (‖H‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg _)
    _ ≤ (D * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (norm_nonneg _)
    _ = D * ‖v‖ ^ 2 := by ring
    _ ≤ D * (G v v / c) := mul_le_mul_of_nonneg_left hnorm hD
    _ = _ := by ring

end PoincareConjecture.Proofs.M09
