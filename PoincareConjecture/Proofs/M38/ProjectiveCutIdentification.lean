import PoincareConjecture.Proofs.M38.ProjectiveCutCollar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable {A B : GeneralizedSliceCarrier.{u}}

noncomputable def interiorCutRegionEquivalence
    {U W : Set A.carrier} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B U V)
    (H : Diffeomorph (𝓡 3) (𝓡 3) B.carrier B.carrier ∞)
    (hH : H '' V ⊆ V) (hW : W = E.inverse '' (H '' V)) :
    SurgeryRegionEquivalence A B W V := by
  have hWU : W ⊆ U := by
    rw [hW]
    exact (image_mono hH).trans E.inverse_image.subset
  have hmap (x : A.carrier) (hx : x ∈ W) : H.symm (E.map x) ∈ V := by
    rw [hW] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    rw [E.right_inverse (hH (mem_image_of_mem H hy)), H.symm_apply_apply]
    exact hy
  have hinverse (y : B.carrier) (hy : y ∈ V) : E.inverse (H y) ∈ W := by
    rw [hW]
    exact mem_image_of_mem _ (mem_image_of_mem _ hy)
  refine {
    map := H.symm ∘ E.map
    inverse := E.inverse ∘ H
    map_image := ?_
    inverse_image := ?_
    left_inverse := ?_
    right_inverse := ?_
    map_smooth := H.symm.contMDiff.comp_contMDiffOn (E.map_smooth.mono hWU)
    inverse_smooth := E.inverse_smooth.comp H.contMDiff.contMDiffOn
      (fun y hy => hH (mem_image_of_mem H hy)) }
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hmap x hx
    · intro y hy
      refine ⟨E.inverse (H y), hinverse y hy, ?_⟩
      change H.symm (E.map (E.inverse (H y))) = y
      rw [E.right_inverse (hH (mem_image_of_mem H hy)), H.symm_apply_apply]
  · rw [image_comp, hW]
  · intro x hx
    change E.inverse (H (H.symm (E.map x))) = x
    rw [H.apply_symm_apply, E.left_inverse (hWU hx)]
  · intro y hy
    change H.symm (E.map (E.inverse (H y))) = y
    rw [E.right_inverse (hH (mem_image_of_mem H hy)), H.symm_apply_apply]

theorem projectiveCut_negative_gluing
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier)
    (H : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞)
    (hH : H '' closure C.first_region ⊆ C.first_region)
    (D : SurgeryBallEmbedding projectiveCarrier.{u})
    (hD : D.closedBallᶜ =
      (puncturedProjectiveRegionEquivalence A C.first_model).inverse ''
        (H '' C.first_region))
    {r : ℝ} (hr : r ≤ 1)
    (hcollar : ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
      D.map ((1 + s) • z.val) =
        (puncturedProjectiveRegionEquivalence A C.first_model).inverse
          (H (C.collar (z, -s)))) :
    let E := interiorCutRegionEquivalence
      (puncturedProjectiveRegionEquivalence A C.first_model) H
      ((image_mono subset_closure).trans hH) hD
    ∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-r) 0 →
      C.collar (z, s) = E.map (D.map ((1 - s) • z.val)) := by
  intro E z s hs
  have hsr : |-s| < r := by rw [abs_neg, abs_of_neg hs.2]; linarith [hs.1]
  have hs1 : s ∈ Ioo (-1 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
  have hU : C.collar (z, s) ∈ C.first_region :=
    (projectiveDouble_collar_first_iff C z hs1).mpr hs.2
  have hHU : H (C.collar (z, s)) ∈ C.first_region :=
    hH (mem_image_of_mem _ (subset_closure hU))
  change C.collar (z, s) = H.symm
    ((puncturedProjectiveRegionEquivalence A C.first_model).map
      (D.map ((1 - s) • z.val)))
  rw [sub_eq_add_neg, hcollar z (-s) hsr, neg_neg,
    (puncturedProjectiveRegionEquivalence A C.first_model).right_inverse hHU,
    H.symm_apply_apply]

theorem projectiveCut_positive_gluing
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier)
    (H : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞)
    (hH : H '' closure C.second_region ⊆ C.second_region)
    (D : SurgeryBallEmbedding projectiveCarrier.{u})
    (hD : D.closedBallᶜ =
      (puncturedProjectiveRegionEquivalence A C.second_model).inverse ''
        (H '' C.second_region))
    {r : ℝ} (hr : r ≤ 1)
    (hcollar : ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
      D.map ((1 + s) • z.val) =
        (puncturedProjectiveRegionEquivalence A C.second_model).inverse
          (H (C.collar (z, s)))) :
    let E := interiorCutRegionEquivalence
      (puncturedProjectiveRegionEquivalence A C.second_model) H
      ((image_mono subset_closure).trans hH) hD
    ∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (0 : ℝ) r →
      C.collar (z, s) = E.map (D.map ((1 + s) • z.val)) := by
  have hnegative := projectiveCut_negative_gluing A (reverseProjectiveDouble C)
    H hH D hD hr (by
      intro z s hs
      change D.map ((1 + s) • z.val) =
        (puncturedProjectiveRegionEquivalence A C.second_model).inverse
          (H (C.collar (z, - -s)))
      simpa only [neg_neg] using hcollar z s hs)
  intro E z s hs
  have h := hnegative z (-s) (by constructor <;> linarith [hs.1, hs.2])
  change C.collar (z, - -s) = E.map (D.map ((1 - -s) • z.val)) at h
  simpa only [neg_neg, sub_neg_eq_add] using h

end PoincareConjecture.M38
