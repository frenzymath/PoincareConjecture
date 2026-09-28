import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.PrescribedRectangle



set_option autoImplicit false
noncomputable section
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus 8 1

private def rectangleHeightReverse : P2 →ᴬ[ℝ] P2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    (ContinuousAffineMap.const ℝ P2 1 -
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)

private theorem rectangleHeightReverse_apply (p : P2) :
    rectangleHeightReverse p = (p.1, 1 - p.2) := rfl

private theorem rectangleHeightReverse_involutive :
    Function.Involutive rectangleHeightReverse := by
  intro p
  ext <;> simp [rectangleHeightReverse_apply]

private theorem rectangleHeightReverse_mapsTo : MapsTo rectangleHeightReverse Rect Rect := by
  rintro p ⟨hp, ht⟩
  exact ⟨hp, by constructor <;> dsimp [rectangleHeightReverse_apply] <;>
    linarith [ht.1, ht.2]⟩

private def rectangleHeightHomeomorph : P2 ≃ₜ P2 where
  toFun := rectangleHeightReverse
  invFun := rectangleHeightReverse
  left_inv := rectangleHeightReverse_involutive
  right_inv := rectangleHeightReverse_involutive
  continuous_toFun := rectangleHeightReverse.continuous
  continuous_invFun := rectangleHeightReverse.continuous

private theorem rectangleHeightReverse_image : rectangleHeightReverse '' Rect = Rect :=
  Subset.antisymm (image_subset_iff.mpr rectangleHeightReverse_mapsTo)
    (fun p hp => ⟨rectangleHeightReverse p, rectangleHeightReverse_mapsTo hp,
      rectangleHeightReverse_involutive p⟩)

private theorem rectangleHeightReverse_frontier :
    rectangleHeightReverse '' frontier Rect = frontier Rect := by
  have h := rectangleHeightHomeomorph.image_frontier Rect
  change rectangleHeightReverse '' frontier Rect = frontier (rectangleHeightReverse '' Rect) at h
  rwa [rectangleHeightReverse_image] at h

private theorem rectangleHeightReverse_frontier_iff (p : P2) :
    rectangleHeightReverse p ∈ frontier Rect ↔ p ∈ frontier Rect := by
  nth_rw 1 [← rectangleHeightReverse_frontier]
  exact rectangleHeightReverse_involutive.injective.mem_set_image

private theorem rectangleHeightReverse_finitePL :
    FinitePiecewiseAffineOn rectangleHeightReverse Rect := by
  have h := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := h
  exact ⟨K, hK, hKs, K.affineOnFaces_affine rectangleHeightReverse⟩

theorem FourSidedProperComplementDisk.exists_normalized_original_rectangle
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R Q : Set X} {center : Set P2}
    {c : P2 → P2} {f : P2 → X} {τ : C3 → X}
    (M : FourSidedProperComplementDisk c f Q center)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hf : PolyhedralPLInCharts e f Ann) (hfi : InjOn f Ann)
    (hfproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (side : Bool) (hτ : InjOn τ tube)
    (hpre : Ann ∩ f ⁻¹' (τ '' tube) = c '' source)
    (hsheet : ∀ p ∈ source, f (c p) = τ (originalStripSheet side p)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Rect ∧
      IsEmbedding (fun p : Rect => k p) ∧ MapsTo k Rect Q ∧
      (∀ p ∈ Rect, k p ∈ frontier Q ↔ p ∈ frontier Rect) ∧
      k '' Rect = f '' M.carrier ∧ k '' frontier Rect = f '' frontier M.carrier ∧
      (∀ p ∈ Rect,
        (k p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
        (k p ∈ τ '' TubeExterior.lateral 1 ↔ p.1 = 0 ∨ p.1 = 1)) ∧
      (∀ t ∈ I, k (0,t) = τ (originalStripSheet side (t,-1))) ∧
      (∀ t ∈ I, k (1,t) = τ (originalStripSheet side (t,1))) := by
  obtain ⟨k, hk, hki, hkQ, hkp, him, hfront, _, _, _, _, hparts, hleft, hright⟩ :=
    M.exists_prescribed_original_rectangle hc hci hf hfi hfproper side hτ hpre hsheet
  rcases M.endpoint_order with horder | horder
  · refine ⟨k, hk, hki, hkQ, hkp, him, hfront, hparts, ?_, ?_⟩
    · simpa only [horder.1, horder.2, mul_zero, mul_one, zero_add] using hleft
    · simpa only [horder.1, horder.2, mul_zero, mul_one, zero_add] using hright
  · have hPL : PolyhedralPLInCharts e (k ∘ rectangleHeightReverse) Rect := by
      obtain ⟨K, hK, hKs, hfaces⟩ := rectangleHeightReverse_finitePL
      exact hKs ▸ hk.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hfaces⟩
        (fun p hp => rectangleHeightReverse_mapsTo (hKs.subset hp))
    let : CompactSpace Rect := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    have hemb : IsEmbedding (fun p : Rect => (k ∘ rectangleHeightReverse) p) := by
      apply (hPL.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
      intro p q hpq
      apply Subtype.ext
      apply rectangleHeightReverse_involutive.injective
      exact congrArg Subtype.val (hki.injective
        (a₁ := ⟨rectangleHeightReverse p, rectangleHeightReverse_mapsTo p.property⟩)
        (a₂ := ⟨rectangleHeightReverse q, rectangleHeightReverse_mapsTo q.property⟩) hpq)
    refine ⟨k ∘ rectangleHeightReverse, hPL, hemb, hkQ.comp rectangleHeightReverse_mapsTo,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      exact (hkp _ (rectangleHeightReverse_mapsTo hp)).trans
        (rectangleHeightReverse_frontier_iff p)
    · rw [image_comp, rectangleHeightReverse_image, him]
    · rw [image_comp, rectangleHeightReverse_frontier, hfront]
    · intro p hp
      have h := hparts _ (rectangleHeightReverse_mapsTo hp)
      refine ⟨h.1.trans ?_, h.2⟩
      change (1 - p.2 = 0 ∨ 1 - p.2 = 1) ↔ p.2 = 0 ∨ p.2 = 1
      constructor <;> rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · intro t ht
      have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa only [Function.comp_apply, rectangleHeightReverse_apply, horder.1, horder.2,
        mul_one, mul_zero, add_zero, sub_sub_cancel] using hleft (1-t) ht'
    · intro t ht
      have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa only [Function.comp_apply, rectangleHeightReverse_apply, horder.1, horder.2,
        mul_one, mul_zero, add_zero, sub_sub_cancel] using hright (1-t) ht'

end PoincareConjecture.M76.Dehn.Annuli
