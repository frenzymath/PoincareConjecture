import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.OriginalTriangleNormalization

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.TriangleCorner

theorem exists_components_homeomorph_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (H : X ≃ₜ Y) :
    ∃ C : ConnectedComponents X ≃ₜ ConnectedComponents Y,
      ∀ x, C (ConnectedComponents.mk x) = ConnectedComponents.mk (H x) := by
  refine ⟨{
    toFun := H.continuous.connectedComponentsMap
    invFun := H.symm.continuous.connectedComponentsMap
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := H.continuous.connectedComponentsMap_continuous
    continuous_invFun := H.symm.continuous.connectedComponentsMap_continuous }, ?_⟩
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp only [Continuous.connectedComponentsMap_mk, H.symm_apply_apply]
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp only [Continuous.connectedComponentsMap_mk, H.apply_symm_apply]
  · intro x
    rfl

theorem normalization_image_component_closure
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {F : (ℝ × ℝ) → E} {R : E → ℝ × ℝ}
    (hF : Continuous F) (hR : Continuous R) (hRF : Function.LeftInverse R F)
    {T : Set (ℝ × ℝ)} {x : ℝ × ℝ} (hx : x ∈ T)
    (hcompact : IsCompact (closure (connectedComponentIn T x))) :
    closure (connectedComponentIn (F '' T) (F x)) =
      F '' closure (connectedComponentIn T x) := by
  rw [← normalization_image_component hF hR hRF hx]
  apply Subset.antisymm
  · exact closure_minimal (image_mono subset_closure) (hcompact.image hF).isClosed
  · exact image_closure_subset_closure_image hF

theorem exists_affine_image_square_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (hFi : Function.Injective F) {M : Set (ℝ × ℝ)}
    (C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M)
    (hC : C.IsFinitePL) :
    ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ (F '' M),
      G.IsFinitePL ∧ ∀ x, (G x : E) = F (C x) := by
  obtain ⟨_, ⟨K, hK, hKM, _⟩, _⟩ := hC.symm
  have hF : FinitePiecewiseAffineOn F M :=
    ⟨K, hK, hKM, K.affineOnFaces_affine F⟩
  obtain ⟨H, hH, hHval⟩ := hF.exists_homeomorph_image hFi.injOn
  exact ⟨C.trans H, hC.trans hH, fun x => hHval (C x)⟩

end PoincareConjecture.M76.TriangleCorner
