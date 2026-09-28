import PoincareConjecture.Proofs.M76.Mathlib.ContractibleConvexExtension
import Mathlib.Analysis.Convex.Intrinsic










set_option autoImplicit false

open Set

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Y] [ContractibleSpace Y]





theorem exists_intrinsicFrontier_extension_of_contractible {s : Set E}
    (hs : IsCompact s) (hc : Convex ℝ s) (hne : s.Nonempty)
    (f : C(intrinsicFrontier ℝ s, Y)) :
    ∃ g : C(s, Y), ∀ x : intrinsicFrontier ℝ s,
      g ⟨x, intrinsicFrontier_subset hs.isClosed x.property⟩ = f x := by
  obtain ⟨p, hp⟩ := hne
  let A := affineSpan ℝ s
  let pA : A := ⟨p, subset_affineSpan ℝ s hp⟩
  let : Nonempty A := ⟨pA⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ pA
  let a : A.direction →ᵃⁱ[ℝ] E := A.subtypeₐᵢ.comp e.toAffineIsometry
  let C : Set A.direction := a ⁻¹' s
  let B : Set A := Subtype.val ⁻¹' s
  have hrange : s ⊆ range a := by
    intro x hx
    refine ⟨e.symm ⟨x, subset_affineSpan ℝ s hx⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, subset_affineSpan ℝ s hx⟩)
  have hCcompact : IsCompact C := a.isometry.isEmbedding.isInducing.isCompact_preimage' hs hrange
  have hCconvex : Convex ℝ C := hc.affine_preimage a.toAffineMap
  have hCinterior : (interior C).Nonempty := by
    obtain ⟨_, q, hq, rfl⟩ := Set.Nonempty.intrinsicInterior hc ⟨p, hp⟩
    change (interior (e.toHomeomorph ⁻¹' B)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    refine ⟨e.symm q, ?_⟩
    change e (e.symm q) ∈ interior B
    rwa [e.apply_symm_apply]
  have hfrontier : a '' frontier C = intrinsicFrontier ℝ s := by
    change (Subtype.val ∘ e.toHomeomorph) '' frontier (e.toHomeomorph ⁻¹' B) =
      Subtype.val '' frontier B
    rw [← e.toHomeomorph.preimage_frontier]
    calc
      (Subtype.val ∘ e.toHomeomorph) '' (e.toHomeomorph ⁻¹' frontier B) =
          Subtype.val '' (e.toHomeomorph '' (e.toHomeomorph ⁻¹' frontier B)) := by
        rw [image_image]
        rfl
      _ = Subtype.val '' frontier B := by
        rw [e.toHomeomorph.surjective.image_preimage]
  let b : C ≃ₜ s := a.isometry.isEmbedding.homeomorphOfSubsetRange hrange
  let d : frontier C ≃ₜ intrinsicFrontier ℝ s :=
    (a.isometry.isEmbedding.homeomorphImage (frontier C)).trans (Homeomorph.setCongr hfrontier)
  obtain ⟨g, hg⟩ := exists_convexBody_extension_of_contractible hCcompact.isClosed hCconvex
    hCinterior hCcompact.isBounded (f.comp ⟨d, d.continuous⟩)
  refine ⟨g.comp ⟨b.symm, b.symm.continuous⟩, ?_⟩
  intro x
  let z := d.symm x
  have hdz : a z = (x : E) := congrArg Subtype.val (d.apply_symm_apply x)
  have hcomm : b.symm ⟨x, intrinsicFrontier_subset hs.isClosed x.property⟩ =
      ⟨z, hCcompact.isClosed.frontier_subset z.property⟩ := by
    apply b.injective
    rw [b.apply_symm_apply]
    exact Subtype.ext hdz.symm
  change g (b.symm ⟨x, intrinsicFrontier_subset hs.isClosed x.property⟩) = f x
  rw [hcomm, hg]
  exact congrArg f (d.apply_symm_apply x)

end ContinuousMap
