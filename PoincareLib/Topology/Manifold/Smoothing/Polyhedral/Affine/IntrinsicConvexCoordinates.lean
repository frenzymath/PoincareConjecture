import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.ContractibleIntrinsicExtension

/-!
# Intrinsic affine coordinates of a compact convex set

Translation from its affine-span direction space makes a nonempty
compact convex set into a full-dimensional convex body, with the
correct frontier. See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/

set_option autoImplicit false

open Set

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation from the direction space parametrizes an affine
subspace isometrically. See Cairns pp. 803--805 and M76 derivation 64. -/
noncomputable def directionCoordinates (A : AffineSubspace ℝ E) (p : A) :
    A.direction →ᵃⁱ[ℝ] E := by
  let : Nonempty A := ⟨p⟩
  exact A.subtypeₐᵢ.comp (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry

/-- Intrinsic coordinates add the chosen origin to the included
direction. See Cairns pp. 803--805 and M76 derivation 64. -/
theorem directionCoordinates_apply (A : AffineSubspace ℝ E) (p : A) (x : A.direction) :
    A.directionCoordinates p x = (x : E) + (p : E) := rfl

/-- The intrinsic coordinate image is the entire affine subspace.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem range_directionCoordinates (A : AffineSubspace ℝ E) (p : A) :
    range (A.directionCoordinates p) = (A : Set E) := by
  let : Nonempty A := ⟨p⟩
  change range (Subtype.val ∘ (AffineIsometryEquiv.vaddConst ℝ p)) = _
  rw [range_comp, (AffineIsometryEquiv.vaddConst ℝ p).surjective.range_eq]
  simp

variable [FiniteDimensional ℝ E]

/-- A compact convex set is a full-dimensional convex body in its
intrinsic coordinates; the frontier image is its intrinsic frontier.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem convexBody_directionCoordinates {S : Set E} (hS : IsCompact S)
    (hc : Convex ℝ S) (p : affineSpan ℝ S) :
    let a := (affineSpan ℝ S).directionCoordinates p
    IsCompact (a ⁻¹' S) ∧ Convex ℝ (a ⁻¹' S) ∧ (interior (a ⁻¹' S)).Nonempty ∧
      a '' (a ⁻¹' S) = S ∧ a '' frontier (a ⁻¹' S) = intrinsicFrontier ℝ S := by
  let A := affineSpan ℝ S
  let : Nonempty A := ⟨p⟩
  let e := AffineIsometryEquiv.vaddConst ℝ p
  let a := A.directionCoordinates p
  have hrange : S ⊆ range a := by
    rw [range_directionCoordinates]
    exact subset_affineSpan ℝ S
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp h
    have hp : (p : E) ∈ (⊥ : AffineSubspace ℝ E) := by
      simpa only [he, span_empty] using p.property
    exact notMem_bot ℝ E (p : E) hp
  refine ⟨a.isometry.isEmbedding.isInducing.isCompact_preimage' hS hrange,
    hc.affine_preimage a.toAffineMap, ?_, image_preimage_eq_of_subset hrange, ?_⟩
  · obtain ⟨_, q, hq, rfl⟩ := Set.Nonempty.intrinsicInterior hc hne
    change (interior (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' S : Set A))).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    refine ⟨e.symm q, ?_⟩
    change e (e.symm q) ∈ interior (Subtype.val ⁻¹' S : Set A)
    rwa [e.apply_symm_apply]
  · change (Subtype.val ∘ e.toHomeomorph) ''
        frontier (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' S : Set A)) =
      Subtype.val '' frontier (Subtype.val ⁻¹' S : Set A)
    rw [← e.toHomeomorph.preimage_frontier]
    calc
      (Subtype.val ∘ e.toHomeomorph) ''
          (e.toHomeomorph ⁻¹' frontier (Subtype.val ⁻¹' S : Set A)) =
        Subtype.val '' (e.toHomeomorph ''
          (e.toHomeomorph ⁻¹' frontier (Subtype.val ⁻¹' S : Set A))) := by
            rw [image_image]
            rfl
      _ = _ := by rw [e.toHomeomorph.surjective.image_preimage]

end AffineSubspace
