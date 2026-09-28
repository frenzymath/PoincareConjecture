import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex



theorem exists_moved_disk_neighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (M : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (f : E ≃ₜ F) (hf : K.AffineOnFaces f)
    (hMs : M.space = f '' K.space)
    {d rim : Set E} {p : E}
    (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim) (hdK : d ⊆ K.space)
    (hpd : p ∈ d \ rim)
    (hopen : IsOpen ((Subtype.val : K.space → E) ⁻¹' (d \ rim))) :
    ∃ d' rim' : Set F, IsFinitePLBallPair (Fin 2 → ℝ) d' rim' ∧
      d' ⊆ M.space ∧ f p ∈ d' \ rim' ∧
      IsOpen ((Subtype.val : M.space → F) ⁻¹' (d' \ rim')) := by
  have hback (y : F) (hy : y ∈ M.space) : f.symm y ∈ K.space := by
    obtain ⟨x, hx, rfl⟩ := hMs.subset hy
    simpa only [f.symm_apply_apply] using hx
  have hmem (T : Set E) (y : F) : y ∈ f '' T ↔ f.symm y ∈ T := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [f.symm_apply_apply] using hx
    · intro hy
      exact ⟨f.symm y, hy, f.apply_symm_apply y⟩
  refine ⟨f '' d, f '' rim,
    hd.image_of_subset (hf.finitePiecewiseAffineOn hK) hdK f.injective.injOn,
    (image_mono hdK).trans hMs.symm.subset,
    ⟨mem_image_of_mem f hpd.1, ?_⟩, ?_⟩
  · intro h
    exact hpd.2 (by simpa only [f.symm_apply_apply] using (hmem rim (f p)).mp h)
  · let back : M.space → K.space := fun y => ⟨f.symm y, hback y y.property⟩
    have hbackcont : Continuous back :=
      (f.symm.continuous.comp continuous_subtype_val).subtype_mk _
    have heq : (Subtype.val : M.space → F) ⁻¹' (f '' d \ f '' rim) =
        back ⁻¹' ((Subtype.val : K.space → E) ⁻¹' (d \ rim)) := by
      ext y
      change ((y : F) ∈ f '' d ∧ (y : F) ∉ f '' rim) ↔
        (f.symm y ∈ d ∧ f.symm y ∉ rim)
      rw [hmem, hmem]
    rw [heq]
    exact hopen.preimage hbackcont

end Geometry.SimplicialComplex
