import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.ArcHeight
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_finitePL_disk_arc_cutoff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d q W C : Set E} {a b : E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hWq : W ⊆ q) (hab : a ≠ b)
    (hC : IsCompact C) (hCd : C ⊆ d \ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E → ℝ) (K : Set E), FinitePiecewiseAffineOn w d ∧
      IsCompact K ∧ K ⊆ d \ W ∧ C ⊆ K ∧
      (∀ x ∈ d, 0 ≤ w x ∧ w x ≤ ε) ∧
      (∀ x ∈ C, 0 < w x) ∧ (∀ x ∈ d \ K, w x = 0) := by
  obtain ⟨v, hv, hbound⟩ := exists_finitePL_disk_arc_height hd hW hWq hab
  have hpos (x : E) (hx : x ∈ C) : 0 < v x :=
    lt_of_le_of_ne (hbound x (hCd hx).1).1
      (Ne.symm (fun hz ↦ (hCd hx).2 ((hbound x (hCd hx).1).2.2.mp hz)))
  obtain ⟨m, hm, hmin⟩ := hC.exists_forall_le'
    (hv.continuousOn.mono (fun _ hx ↦ (hCd hx).1)) hpos
  let δ := min (m / 2) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos hm) (by norm_num)
  have hδm : δ < m := (min_le_left _ _).trans_lt (half_lt_self hm)
  let K := {x ∈ d | δ ≤ v x}
  have hK : IsCompact K := hd.isCompact.of_isClosed_subset
    (hv.continuousOn.preimage_isClosed_of_isClosed hd.isCompact.isClosed isClosed_Ici)
    inter_subset_left
  have hKd : K ⊆ d \ W := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxW
    have hz := (hbound x hx.1).2.2.mpr hxW
    exact (not_le_of_gt hδ) (hz ▸ hx.2)
  have hCK : C ⊆ K := fun x hx ↦ ⟨(hCd hx).1, hδm.le.trans (hmin x hx)⟩
  let w : E → ℝ := fun x ↦ ε * max 0 (v x - δ)
  let shift : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ δ
  have hw : FinitePiecewiseAffineOn w d :=
    ((hv.postcomp shift).positivePart.postcomp
      (ε • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ ↦ rfl)
  refine ⟨w, K, hw, hK, hKd, hCK, ?_, ?_, ?_⟩
  · intro x hx
    have hupper : max 0 (v x - δ) ≤ 1 := max_le (by norm_num) (by linarith [(hbound x hx).2.1])
    exact ⟨mul_nonneg hε.le (le_max_left _ _),
      (mul_le_mul_of_nonneg_left hupper hε.le).trans_eq (mul_one _)⟩
  · intro x hx
    exact mul_pos hε (lt_max_of_lt_right (sub_pos.mpr (hδm.trans_le (hmin x hx))))
  · intro x hx
    have hlt : v x < δ := lt_of_not_ge (fun hh ↦ hx.2 ⟨hx.1, hh⟩)
    change ε * max 0 (v x - δ) = 0
    rw [max_eq_left (sub_nonpos.mpr hlt.le), mul_zero]

end PoincareConjecture.M76.Dehn.Annuli
