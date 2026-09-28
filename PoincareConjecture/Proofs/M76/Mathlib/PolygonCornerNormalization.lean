import PoincareConjecture.Proofs.M76.Mathlib.AffineBasisEquivalence
import PoincareConjecture.Proofs.M76.Mathlib.PolygonExtremeVertex










set_option autoImplicit false

open Set

private theorem independent_axis_corner :
    AffineIndependent ℝ ![((1 : ℝ), (0 : ℝ)), (0, 0), (0, 1)] := by
  let S : AffineSubspace ℝ (ℝ × ℝ) :=
    (affineSpan ℝ {(1 : ℝ)}).comap
      (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap
  apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := S)
  · norm_num
  · simp [S]
  · simp [S]
  · simp [S]




theorem AffineIndependent.exists_axis_corner_coordinates {a b c : ℝ × ℝ}
    (h : AffineIndependent ℝ ![a, b, c]) :
    ∃ e : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ), e a = (1, 0) ∧ e b = (0, 0) ∧ e c = (0, 1) := by
  let B : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨![a, b, c], h,
    h.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  let C : AffineBasis (Fin 3) ℝ (ℝ × ℝ) :=
    ⟨![(1, 0), (0, 0), (0, 1)], independent_axis_corner,
      independent_axis_corner.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by simp [Module.finrank_prod])⟩
  obtain ⟨e, he⟩ := B.exists_affineEquiv_map C 1
  exact ⟨e.toContinuousAffineEquiv, he 0, he 1, he 2⟩

namespace Polygon





theorem exists_supported_axis_corner {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ (i : Fin (n + 3)) (e : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ))
      (L : (ℝ × ℝ) →ₗ[ℝ] ℝ),
      e (P ((finRotate (n + 3)).symm i)) = (1, 0) ∧
      e (P i) = (0, 0) ∧ e (P (finRotate (n + 3) i)) = (0, 1) ∧
      (∀ j, L (e (P j)) ≤ 0) ∧ 0 < L (-1, -1) := by
  obtain ⟨H, i, _, hmax, hind⟩ := P.exists_nondegenerate_strict_max hP hinj
  obtain ⟨e, hprev, hcenter, hnext⟩ := hind.exists_axis_corner_coordinates
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := H.comp e.symm.toAffineEquiv.linear.toLinearMap
  have hL : ∀ x, L (e x) = H x - H (P i) := by
    intro x
    have hx : e.symm.toAffineEquiv.linear (e x) = x - P i := by
      have he := e.symm.toAffineEquiv.toAffineMap.linearMap_vsub (e x) (e (P i))
      change e.symm.toAffineEquiv.linear (e x - e (P i)) =
        e.symm (e x) - e.symm (e (P i)) at he
      simp only [e.symm_apply_apply] at he
      simpa only [hcenter, show (0, 0) = (0 : ℝ × ℝ) from rfl,
        sub_zero] using he
    change H (e.symm.toAffineEquiv.linear (e x)) = _
    rw [hx, map_sub]
  have hpne : (finRotate (n + 3)).symm i ≠ i := by
    intro heq
    have h := hprev
    rw [heq, hcenter] at h
    norm_num at h
  have hnne : finRotate (n + 3) i ≠ i := by
    intro heq
    have h := hnext
    rw [heq, hcenter] at h
    norm_num at h
  have hp : L (1, 0) < 0 := by
    rw [← hprev, hL]
    exact sub_neg.mpr (hmax _ hpne)
  have hn : L (0, 1) < 0 := by
    rw [← hnext, hL]
    exact sub_neg.mpr (hmax _ hnne)
  refine ⟨i, e, L, hprev, hcenter, hnext, ?_, ?_⟩
  · intro j
    rw [hL]
    by_cases hji : j = i
    · simp only [hji, sub_self, le_refl]
    · exact (sub_neg.mpr (hmax j hji)).le
  · have heq : ((-1 : ℝ), (-1 : ℝ)) = -((1, 0) + (0, 1) : ℝ × ℝ) := by
      ext <;> norm_num
    rw [heq, map_neg, map_add]
    linarith

end Polygon
