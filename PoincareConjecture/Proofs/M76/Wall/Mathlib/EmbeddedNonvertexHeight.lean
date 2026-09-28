import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageReparameterization
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNonvertexHeightChart

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

theorem AffineOnFaces.exists_embedded_nonvertex_height_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    {c : E → F} (hc : K.AffineOnFaces c) (hinj : InjOn c K.space)
    {f : E → ℝ} (hf : K.AffineOnFaces f) {x : E} (hxK : x ∈ K.space)
    (hx : c x ∈ interior (c '' K.space))
    (hreg : ∀ v ∈ K.vertices, f v ≠ f x)
    (B : SimplicialComplex ℝ E) (hBK : B ≤ K) (hxB : x ∈ B.space)
    (psi : F →ᴬ[ℝ] ℝ) (hpsi : ∀ y ∈ B.space, psi (c y) = psi (c x)) :
    ∃ (ell : F →ᴬ[ℝ] ℝ) (w : F) (H : OpenPartialHomeomorph F F),
      ell.contLinear w = 1 ∧ psi.contLinear w = 0 ∧
      c x ∈ H.source ∧ H (c x) = c x ∧
      H.source ⊆ interior (c '' K.space) ∧
      H.target ⊆ interior (c '' K.space) ∧
      H ∈ piecewiseAffineGroupoid F ∧
      (∀ y ∈ K.space, c y ∈ H.source → ell (H (c y)) = f y) ∧
      (∀ y, psi (H y) = psi y) ∧ ∀ y, psi (H.symm y) = psi y := by
  classical
  let u := Function.invFunOn c K.space
  have hleft : LeftInvOn u c K.space := hinj.leftInvOn_invFunOn
  let J := hc.embeddedImage hinj
  have hJ : J.faces.Finite := hc.embeddedImage_finite hinj hK
  have hfJ : J.AffineOnFaces (f ∘ u) :=
    hc.comp_inverse_on_embeddedImage hf hinj hleft
  have hxJ : c x ∈ interior J.space := by
    simpa only [J, hc.embeddedImage_space hinj] using hx
  have hregJ : ∀ v ∈ J.vertices, (f ∘ u) v ≠ (f ∘ u) (c x) := by
    intro v hv
    rw [hc.embeddedImage_vertices hinj] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    change f (u (c z)) ≠ f (u (c x))
    rw [hleft (K.vertices_subset_space hz), hleft hxK]
    exact hreg z hz
  have hcB : B.AffineOnFaces c := fun s hs => hc s (hBK hs)
  have hinjB : InjOn c B.space := hinj.mono (space_subset_of_le hBK)
  let D := hcB.embeddedImage hinjB
  have hDJ : D ≤ J := by
    intro s hs
    change s ∈ (hcB.embeddedImage hinjB).faces at hs
    change s ∈ (hc.embeddedImage hinj).faces
    rw [hcB.embeddedImage_faces hinjB] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hc.embeddedImage_faces hinj]
    exact ⟨t, hBK ht, rfl⟩
  have hxD : c x ∈ D.space := by
    rw [hcB.embeddedImage_space hinjB]
    exact mem_image_of_mem c hxB
  have hpsiD : ∀ y ∈ D.space, psi y = psi (c x) := by
    intro y hy
    rw [hcB.embeddedImage_space hinjB] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hpsi z hz
  obtain ⟨ell, w, H, hellw, hpsiw, hxH, hHx, hHs, hHt, hHPL,
    hheight, hHpsi, hHinv⟩ := J.exists_nonvertex_height_chart_preserving_affine
      hJ hfJ hxJ hregJ D hDJ hxD psi hpsiD
  refine ⟨ell, w, H, hellw, hpsiw, hxH, hHx, ?_, ?_, hHPL, ?_, hHpsi, hHinv⟩
  · simpa only [J, hc.embeddedImage_space hinj] using hHs
  · simpa only [J, hc.embeddedImage_space hinj] using hHt
  · intro y hy hyH
    have h := hheight (c y) hyH
    change ell (H (c y)) = f (u (c y)) at h
    rw [hleft hy] at h
    exact h

end Geometry.SimplicialComplex
