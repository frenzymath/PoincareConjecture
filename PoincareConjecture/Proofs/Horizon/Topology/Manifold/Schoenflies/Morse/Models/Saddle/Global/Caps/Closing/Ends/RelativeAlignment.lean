import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CanonicalAlignment

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

theorem exists_relative_cap_alignment_of_compatible_normalizations
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {d₁ d₂ b s₁ s₂ : Real} (hd₁ : d₁ < b) (hd₂ : d₂ < b)
    (hs₁ : s₁ < 0) (hs₂ : s₂ < 0)
    {C₁ C₂ : Set E3}
    (N₁ N₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hN₁ : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, N₁ y = y)
    (hN₂ : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, N₂ y = y)
    (hagree : EqOn N₁ N₂ {y | b ≤ inner Real v y})
    (hheight : ∀ y, b ≤ inner Real v y → b ≤ inner Real v (N₁ y))
    (himage₁ : N₁ '' C₁ =
      liftPlaneDiffeomorph hv d₁ s₁ hs₁.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) d₁ b)
    (himage₂ : N₂ '' C₂ =
      liftPlaneDiffeomorph hv d₂ s₂ hs₂.ne B '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) d₂ b) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧
        EqOn F id {y | b ≤ inner Real v y} ∧ F '' C₁ = C₂ := by
  obtain ⟨c, _, hcb, K, hK, F, hfix, hhalf, himage⟩ :=
    exists_supported_complete_lower_cap_alignment hv γ hγ A B hA hB hd₁ hd₂ hs₁ hs₂
  obtain ⟨K₁, hK₁, hfix₁⟩ := hN₁
  obtain ⟨K₂, hK₂, hfix₂⟩ := hN₂
  let G := (N₁.trans F).trans N₂.symm
  refine ⟨K₁ ∪ K ∪ K₂, (hK₁.union hK).union hK₂, G, ?_, ?_, ?_⟩
  · intro y hy
    change N₂.symm (F (N₁ y)) = y
    rw [hfix₁ y (fun h => hy (Or.inl (Or.inl h))),
      hfix y (fun h => hy (Or.inl (Or.inr h)))]
    apply N₂.injective
    change N₂ (N₂.symm y) = N₂ y
    rw [N₂.apply_symm_apply, hfix₂ y (fun h => hy (Or.inr h))]
  · intro y hy
    change N₂.symm (F (N₁ y)) = y
    rw [hhalf _ (hcb.le.trans (hheight y hy)), hagree hy, N₂.symm_apply_apply]
  · change (N₂.symm ∘ F ∘ N₁) '' C₁ = C₂
    rw [image_comp, image_comp, himage₁, himage, ← himage₂, image_image]
    simp only [N₂.symm_apply_apply, image_id']

theorem exists_buffered_relative_cap_alignment_of_compatible_normalizations
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {d₁ d₂ b s₁ s₂ : Real} (hd₁ : d₁ < b) (hd₂ : d₂ < b)
    (hs₁ : s₁ < 0) (hs₂ : s₂ < 0)
    {C₁ C₂ : Set E3}
    (N₁ N₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hN₁ : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, N₁ y = y)
    (hN₂ : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, N₂ y = y)
    {δ : Real} (hδ : 0 < δ)
    (hagree : EqOn N₁ N₂ {y | b - δ ≤ inner Real v y})
    (hheight : ∀ y, b - δ ≤ inner Real v y → inner Real v (N₁ y) = inner Real v y)
    (himage₁ : N₁ '' C₁ =
      liftPlaneDiffeomorph hv d₁ s₁ hs₁.ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) d₁ b)
    (himage₂ : N₂ '' C₂ =
      liftPlaneDiffeomorph hv d₂ s₂ hs₂.ne B '' boundedCylinderNorthernCap v ∪
        terminalCylinder (range γ) d₂ b) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧
        (∃ η : Real, 0 < η ∧ EqOn F id {y | b - η ≤ inner Real v y}) ∧ F '' C₁ = C₂ := by
  obtain ⟨c, _, hcb, K, hK, F, hfix, hhalf, himage⟩ :=
    exists_supported_complete_lower_cap_alignment hv γ hγ A B hA hB hd₁ hd₂ hs₁ hs₂
  obtain ⟨K₁, hK₁, hfix₁⟩ := hN₁
  obtain ⟨K₂, hK₂, hfix₂⟩ := hN₂
  let η := min δ ((b - c) / 2)
  have hη : 0 < η := lt_min hδ (by linarith)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηc : η ≤ (b - c) / 2 := min_le_right _ _
  let G := (N₁.trans F).trans N₂.symm
  refine ⟨K₁ ∪ K ∪ K₂, (hK₁.union hK).union hK₂, G, ?_, ?_, ?_⟩
  · intro y hy
    change N₂.symm (F (N₁ y)) = y
    rw [hfix₁ y (fun h => hy (Or.inl (Or.inl h))),
      hfix y (fun h => hy (Or.inl (Or.inr h)))]
    apply N₂.injective
    change N₂ (N₂.symm y) = N₂ y
    rw [N₂.apply_symm_apply, hfix₂ y (fun h => hy (Or.inr h))]
  · refine ⟨η, hη, ?_⟩
    intro y hy
    have hyδ : b - δ ≤ inner Real v y := by change b - η ≤ inner Real v y at hy; linarith
    change N₂.symm (F (N₁ y)) = y
    rw [hhalf _ (by rw [hheight y hyδ]; change b - η ≤ inner Real v y at hy; linarith),
      hagree hyδ, N₂.symm_apply_apply]
  · change (N₂.symm ∘ F ∘ N₁) '' C₁ = C₂
    rw [image_comp, image_comp, himage₁, himage, ← himage₂, image_image]
    simp only [N₂.symm_apply_apply, image_id']

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
