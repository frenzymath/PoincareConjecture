import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1



theorem intrinsic_disk_parameter_image {X E : Type*}
    (F : X → E) (j : V2 → X) (u : E → V2)
    (hu : ∀ z : D, u (F (j z)) = (z : V2)) :
    InjOn u (F '' (j '' D)) ∧ u '' (F '' (j '' D)) = D := by
  constructor
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩ h
    have hzv : z = v := (hu ⟨z, hz⟩).symm.trans (h.trans (hu ⟨v, hv⟩))
    exact congrArg (fun x => F (j x)) hzv
  · apply Subset.antisymm
    · rintro _ ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      rw [hu ⟨z, hz⟩]
      exact hz
    · intro z hz
      exact ⟨F (j z), ⟨j z, ⟨z, hz, rfl⟩, rfl⟩, hu ⟨z, hz⟩⟩




theorem intrinsic_disk_face_dimensions
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : X → E) (j : V2 → X) (u : E → V2)
    (hspace : K.space = F '' (j '' D))
    (hu : ∀ z : D, u (F (j z)) = (z : V2)) (hf : K.AffineOnFaces u) :
    (∀ s ∈ K.faces, s.card ≤ 3) ∧
      ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  classical
  obtain ⟨hinj, himage⟩ := intrinsic_disk_parameter_image F j u hu
  have hi : InjOn u K.space := hspace.symm ▸ hinj
  let L := hf.embeddedImage hi
  have hL : L.faces.Finite := hf.embeddedImage_finite hi hK
  have hLs : L.space = D := by
    rw [hf.embeddedImage_space, hspace, himage]
  refine ⟨?_, ?_⟩
  · intro s hs
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      hf.face_card_le_of_injOn hi hs
  · intro s hs
    have hsL : s.image u ∈ L.faces :=
      (hf.image_mem_embeddedImage_iff hi (K.subset_space hs)).mpr hs
    have hcv : Convex ℝ L.space := hLs.symm ▸ convex_closedBall (0 : V2) 1
    have hint : (interior L.space).Nonempty := by
      rw [hLs, interior_closedBall']
      exact ⟨0, mem_ball_self zero_lt_one⟩
    obtain ⟨t, ht, hst, htc⟩ := L.exists_full_coface_of_convex_space hL hcv hint hsL
    obtain ⟨v, hv, hsv, hvc, _⟩ := hf.pullback_embeddedImage_coface hi hs ht hst
      (show t.card = 3 by simpa using htc)
    exact ⟨v, hv, hsv, hvc⟩

end PoincareConjecture.M76
