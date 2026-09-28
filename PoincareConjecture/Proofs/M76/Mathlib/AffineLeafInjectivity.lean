import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafInverse










set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem projKer_affineLeafMap_sub_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    (z : F × (Q x0).ker) :
    (Q x0).projKerOfRightInverse a.contLinear h0 (a.affineLeafMap Q x0 z - a 0) = z.2 := by
  have ha : a z.1 - a 0 = a.contLinear z.1 := by
    simpa using (a.contLinear_map_vsub z.1 0).symm
  have he : a.affineLeafMap Q x0 z - a 0 =
      (a.affineLeafMap Q x0 z - a z.1) + a.contLinear z.1 := by
    rw [← ha]
    abel
  rw [he, map_add, a.projKer_affineLeafMap_sub Q x0 h0,
    ContinuousLinearMap.projKerOfRightInverse_comp_inv, add_zero]



theorem apply_affineLeafMap_sub_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    (z : F × (Q x0).ker) :
    Q x0 (a.affineLeafMap Q x0 z - a 0) = z.1 - Q z.1 z.2 := by
  have ha : a z.1 - a 0 = a.contLinear z.1 := by
    simpa using (a.contLinear_map_vsub z.1 0).symm
  have he : a.affineLeafMap Q x0 z - a 0 =
      (a z.1 - a 0) + (z.2 : E) - a.contLinear (Q z.1 z.2) := by
    unfold affineLeafMap
    abel
  have hz : Q x0 (z.2 : E) = 0 := z.2.property
  rw [he, map_sub, map_add, ha, h0, h0, hz, add_zero]





theorem injOn_affineLeafMap_of_lipschitz (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    {C : Set F} {K : ℝ≥0} (hQ : LipschitzOnWith K Q C) :
    InjOn (a.affineLeafMap Q x0) (C ×ˢ {z : (Q x0).ker | (K : ℝ) * ‖z‖ < 1}) := by
  intro u hu v hv he
  have hz : u.2 = v.2 := by
    have h := congrArg (fun w => (Q x0).projKerOfRightInverse a.contLinear h0 (w - a 0)) he
    simpa only [a.projKer_affineLeafMap_sub_zero Q x0 h0] using h
  have hc := congrArg (fun w => Q x0 (w - a 0)) he
  rw [a.apply_affineLeafMap_sub_zero Q x0 h0,
    a.apply_affineLeafMap_sub_zero Q x0 h0, ← hz] at hc
  have hd : u.1 - v.1 = (Q u.1 - Q v.1) (u.2 : E) := by
    change u.1 - v.1 = Q u.1 (u.2 : E) - Q v.1 (u.2 : E)
    calc
      u.1 - v.1 = (Q u.1 (u.2 : E) + (u.1 - Q u.1 (u.2 : E))) - v.1 := by abel
      _ = (Q u.1 (u.2 : E) + (v.1 - Q v.1 (u.2 : E))) - v.1 := by rw [hc]
      _ = _ := by abel
  have hbound : ‖Q u.1 - Q v.1‖ ≤ (K : ℝ) * ‖u.1 - v.1‖ := by
    simpa only [dist_eq_norm] using hQ.dist_le_mul u.1 hu.1 v.1 hv.1
  have hop := (Q u.1 - Q v.1).le_opNorm (u.2 : E)
  have hmul := mul_le_mul_of_nonneg_right hbound (norm_nonneg (u.2 : E))
  have hsmall : (K : ℝ) * ‖(u.2 : E)‖ < 1 := hu.2
  have hzbase : ‖u.1 - v.1‖ = 0 := by
    rw [← hd] at hop
    nlinarith [norm_nonneg (u.1 - v.1)]
  exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hzbase)) hz




theorem exists_pos_injOn_affineLeafMap (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    {C : Set F} {K : ℝ≥0} (hQ : LipschitzOnWith K Q C) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn (a.affineLeafMap Q x0)
      (C ×ˢ Metric.ball (0 : (Q x0).ker) ε) := by
  let ε : ℝ := ((K : ℝ) + 1)⁻¹
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hKε : (K : ℝ) * ε < 1 := by
    change (K : ℝ) * ((K : ℝ) + 1)⁻¹ < 1
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    linarith
  refine ⟨ε, inv_pos.mpr hden, (a.injOn_affineLeafMap_of_lipschitz Q x0 h0 hQ).mono ?_⟩
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  refine ⟨hx, lt_of_le_of_lt ?_ hKε⟩
  exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hz).le K.coe_nonneg




theorem exists_pos_injOn_affineLeafMap_of_compact (a : F →ᴬ[ℝ] E)
    (Q : F → E →L[ℝ] F) (x0 : F)
    (h0 : Function.RightInverse a.contLinear (Q x0)) {C : Set F}
    (hC : IsCompact C) (hc : Convex ℝ C) (hQ : ContDiffOn ℝ 1 Q C) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn (a.affineLeafMap Q x0)
      (C ×ˢ Metric.ball (0 : (Q x0).ker) ε) := by
  obtain ⟨K, hK⟩ := hQ.exists_lipschitzOnWith one_ne_zero hc hC
  exact a.exists_pos_injOn_affineLeafMap Q x0 h0 hK

end ContinuousAffineMap
