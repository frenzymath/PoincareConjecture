import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.OriginalChart.ClippedDisks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages



set_option autoImplicit false
open Set Geometry

namespace Geometry

theorem FinitePiecewiseAffineOn.exists_image_interior_disk
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Set E} {f : E → F} (hf : FinitePiecewiseAffineOn f K)
    (hfi : InjOn f K) {x : E} (hx : x ∈ interior K)
    (P : SimplicialComplex ℝ F) (hPs : P.space = f '' K) :
    ∃ d rim : Set F, IsFinitePLBallPair E d rim ∧ d ⊆ P.space ∧
      f x ∈ d \ rim ∧ IsOpen ((Subtype.val : P.space → F) ⁻¹' (d \ rim)) := by
  obtain ⟨B, hB, hBcv, hxB, hBK⟩ := isOpen_interior.exists_finite_convex_neighborhood hx
  have hsub : B.space ⊆ K := hBK.trans interior_subset
  have hpair : IsFinitePLBallPair E B.space (frontier B.space) :=
    isFinitePLBallPair_of_compact_convex (B.isCompact_space_of_finite hB)
      hBcv ⟨x, hxB⟩ B hB rfl
  have hfront : frontier B.space ⊆ K := hpair.1.trans hsub
  have hball := hpair.image_of_subset hf hsub hfi
  obtain ⟨H, hH, hHval⟩ := hf.exists_homeomorph_image hfi
  let H' : K ≃ₜ P.space := H.trans (Homeomorph.setCongr hPs.symm)
  have hH' (y : K) : (H' y : F) = f y := hHval y
  have hin (y : E) (hy : y ∈ K) :
      f y ∈ f '' B.space \ f '' frontier B.space ↔ y ∈ interior B.space := by
    constructor
    · rintro ⟨⟨z, hz, heq⟩, hn⟩
      have hzy : z = y := hfi (hsub hz) hy heq
      have hyB : y ∈ B.space := hzy ▸ hz
      have hyfront : y ∉ frontier B.space := fun hh => hn ⟨y, hh, rfl⟩
      exact (self_sdiff_frontier B.space).subset ⟨hyB, hyfront⟩
    · intro hyB
      refine ⟨⟨y, interior_subset hyB, rfl⟩, ?_⟩
      rintro ⟨z, hz, heq⟩
      have hzy : z = y := hfi (hfront hz) hy heq
      exact ((self_sdiff_frontier B.space).symm.subset hyB).2 (hzy ▸ hz)
  refine ⟨f '' B.space, f '' frontier B.space, hball,
    (image_mono hsub).trans hPs.symm.subset, (hin x (interior_subset hx)).mpr hxB, ?_⟩
  have heq : (Subtype.val : P.space → F) ⁻¹' (f '' B.space \ f '' frontier B.space) =
      H' '' ((Subtype.val : K → E) ⁻¹' interior B.space) := by
    ext y
    constructor
    · intro hy
      change (y : F) ∈ f '' B.space \ f '' frontier B.space at hy
      refine ⟨H'.symm y, ?_, H'.apply_symm_apply y⟩
      apply (hin (H'.symm y) (H'.symm y).property).mp
      have hv : f (H'.symm y) = (y : F) :=
        (hH' (H'.symm y)).symm.trans (congrArg Subtype.val (H'.apply_symm_apply y))
      simpa only [hv] using hy
    · rintro ⟨z, hz, rfl⟩
      change (H' z : F) ∈ f '' B.space \ f '' frontier B.space
      rw [hH']
      exact (hin z z.property).mpr hz
  rw [heq]
  exact H'.isOpenMap _ (isOpen_interior.preimage continuous_subtype_val)

end Geometry
