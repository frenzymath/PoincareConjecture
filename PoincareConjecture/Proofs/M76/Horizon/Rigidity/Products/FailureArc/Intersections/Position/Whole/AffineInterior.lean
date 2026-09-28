import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import Mathlib.Analysis.Convex.Intrinsic

set_option autoImplicit false

open Set

namespace AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem intrinsicInterior_image_of_injOn (f : E →ᵃ[ℝ] F) (s : Set E)
    (hf : InjOn f (affineSpan ℝ s)) :
    intrinsicInterior ℝ (f '' s) = f '' intrinsicInterior ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let A := affineSpan ℝ s
  let B := affineSpan ℝ (f '' s)
  let : Nonempty A := ⟨⟨hs.choose, subset_affineSpan ℝ s hs.choose_spec⟩⟩
  let : Nonempty B := ⟨⟨f hs.choose,
    subset_affineSpan ℝ (f '' s) (mem_image_of_mem f hs.choose_spec)⟩⟩
  have hmap : A.map f = B := AffineSubspace.map_span f s
  let g : A →ᵃ[ℝ] B := f.restrict hmap.le
  have hginj : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hf x.property y.property (congrArg Subtype.val hxy))
  let e : A ≃ᵃ[ℝ] B := AffineEquiv.ofBijective
    ⟨hginj, AffineMap.restrict.surjective f hmap⟩
  let h := e.toContinuousAffineEquiv.toHomeomorph
  have hpre : h '' (Subtype.val ⁻¹' s : Set A) =
      (Subtype.val ⁻¹' (f '' s) : Set B) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, subset_affineSpan ℝ s hx⟩, hx, ?_⟩
      exact Subtype.ext hxy
  change Subtype.val '' interior (Subtype.val ⁻¹' (f '' s) : Set B) =
    f '' (Subtype.val '' interior (Subtype.val ⁻¹' s : Set A))
  rw [← hpre, ← h.image_interior, image_image, image_image]
  rfl

end AffineMap
