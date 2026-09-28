import PoincareConjecture.Proofs.M76.Mathlib.StarConvexCellComplement
import Mathlib.Analysis.Normed.Module.Ball.Pointwise











set_option autoImplicit false

open Set Metric
open scoped Pointwise






theorem isSimplyConnected_prod_ball_sdiff_closedBall_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : 2 < Module.finrank ℝ (E × F))
    {r a b : ℝ} (hr : 0 ≤ r) (hra : r < a) (hb : 0 < b) :
    IsSimplyConnected ((ball (0 : E) a ×ˢ ball (0 : F) b) \
      (closedBall (0 : E) r ×ˢ {(0 : F)})) := by
  have ha : 0 < a := hr.trans_lt hra
  let L : (E × F) ≃ₗ[ℝ] E × F :=
    (LinearEquiv.smulOfNeZero ℝ E a ha.ne').prodCongr
      (LinearEquiv.smulOfNeZero ℝ F b hb.ne')
  let H : (E × F) ≃ₜ E × F := L.toContinuousLinearEquiv.toHomeomorph
  let W : Set (E × F) := ball (0 : E) a ×ˢ ball (0 : F) b
  let C : Set (E × F) := closedBall (0 : E) r ×ˢ {(0 : F)}
  let D : Set (E × F) := H ⁻¹' C
  have hbox : H '' ball (0 : E × F) 1 = W := by
    change H '' ball ((0 : E), (0 : F)) 1 = W
    rw [← ball_prod_same (0 : E) (0 : F) (1 : ℝ)]
    change Prod.map (fun x : E => a • x) (fun y : F => b • y) ''
      (ball (0 : E) 1 ×ˢ ball (0 : F) 1) = W
    rw [prodMap_image_prod]
    change (a • ball (0 : E) 1) ×ˢ (b • ball (0 : F) 1) = W
    rw [_root_.smul_ball ha.ne', _root_.smul_ball hb.ne']
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb, mul_one, W]
  have hboxpre : H ⁻¹' W = ball (0 : E × F) 1 := by
    rw [← hbox, H.injective.preimage_image]
  have hC : IsCompact C := (isCompact_closedBall (0 : E) r).prod isCompact_singleton
  have hcv : Convex ℝ C := (convex_closedBall (0 : E) r).prod (convex_singleton (0 : F))
  have hC0 : (0 : E × F) ∈ C := ⟨mem_closedBall_self hr, mem_singleton _⟩
  have hCW : C ⊆ W := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy0 : y = 0 := hy
    exact ⟨closedBall_subset_ball hra hx, hy0.symm ▸ mem_ball_self hb⟩
  have hD : IsCompact D := H.isClosedEmbedding.isCompact_preimage hC
  have hDcv : Convex ℝ D := by
    change Convex ℝ (L.toLinearMap ⁻¹' C)
    exact hcv.linear_preimage L.toLinearMap
  have hD0 : (0 : E × F) ∈ D := by
    change L (0 : E × F) ∈ C
    rw [map_zero]
    exact hC0
  have hDb : D ⊆ ball (0 : E × F) 1 := by
    rw [← hboxpre]
    exact fun _ hx => hCW hx
  have hsc := isSimplyConnected_ball_sdiff_compact_convex_of_two_lt_finrank
    hdim hD hDcv hD0 hDb
  apply (H.isSimplyConnected_preimage (s := W \ C)).mp
  rw [preimage_sdiff, hboxpre]
  exact hsc




theorem isSimplyConnected_product_cell_tube
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : 2 < Module.finrank ℝ (E × F))
    {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    IsSimplyConnected ((ball (0 : E) (r + ε) ×ˢ ball (0 : F) ε) \
      (closedBall (0 : E) r ×ˢ {(0 : F)})) :=
  isSimplyConnected_prod_ball_sdiff_closedBall_zero hdim hr (lt_add_of_pos_right r hε) hε
