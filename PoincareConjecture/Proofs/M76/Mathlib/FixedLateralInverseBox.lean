import PoincareConjecture.Proofs.M76.Mathlib.FixedLateralInversePrism
import PoincareConjecture.Proofs.M76.Mathlib.LongitudinalPrismCoordinates












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem IsFinitePL.exists_fixed_lateral_inverse_box
    {S surface : Set E} {T : Set ((ℝ × ℝ) × ℝ)} {e : S ≃ₜ T}
    (he : e.IsFinitePL) (hdim : Module.finrank ℝ E = 3)
    (A : E → ℝ) (hheight : ∀ x : S, (e x : (ℝ × ℝ) × ℝ).1.1 = A x)
    (hplane : ∀ x : S, (e x : (ℝ × ℝ) × ℝ).2 = 0 ↔ (x : E) ∈ surface)
    (σ : Bool → ℝ) (hσ : σ false < σ true)
    (haxis : ∀ s ∈ Icc (σ false) (σ true), ((0, s), 0) ∈ interior T)
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    {r : ℝ} (hr : 0 < r) (hbox : ∀ j, f j '' box r ⊆ interior S)
    (hkeep : ∀ j (x : S), (x : E) ∈ f j '' box r →
      (e x : (ℝ × ℝ) × ℝ) = L j x)
    (hlateral : ∀ j t z, L j (f j ((t, 0), z)) = ((t, σ j), z)) :
    ∃ (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ)) (δ : ℝ)
      (F : ((ℝ × ℝ) × ℝ) → E),
      δ ∈ Ioo 0 r ∧ H.source = interior S ∧ H.target = interior T ∧
      (∀ x : S, H x = (e x : (ℝ × ℝ) × ℝ)) ∧
      (∀ y : T, H.symm y = (e.symm y : E)) ∧
      F = H.symm ∘ longitudinalPrismCoordinates δ (σ false) (σ true) ∧
      (Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ ⊆ H.target ∧
      FinitePiecewiseAffineOn F (box δ) ∧ InjOn F (box δ) ∧
      F '' box δ =
        H.symm '' ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ) ∧
      F '' boxBoundary δ =
        H.symm '' frontier ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (F '' box δ) (F '' boxBoundary δ) ∧
      (∀ j, f j '' box δ ⊆ H.source) ∧
      (∀ j x, x ∈ box δ → H (f j x) = L j (f j x)) ∧
      (∀ x ∈ box δ, A (F x) = x.1.1) ∧
      (∀ x ∈ box δ, F x ∈ surface ↔ x.2 = 0) ∧
      ∀ j t z, t ∈ Icc (-δ) δ → z ∈ Icc (-δ) δ →
        F ((t, if j then δ else -δ), z) = f j ((t, 0), z) := by
  obtain ⟨H, δ, hδ, hsource, htarget, _, _, _, _, hHe, hInvHe,
    hPT, hInvP, hInjP, hPrismPair, hboxSource, hforward,
    hInvHeight, hInvPlane, hInvLateral⟩ :=
    he.exists_interior_chart_with_fixed_lateral_prism hdim A hheight hplane σ hσ
      haxis f L hr hbox hkeep hlateral
  let N := longitudinalPrismCoordinates δ (σ false) (σ true)
  let F : ((ℝ × ℝ) × ℝ) → E := H.symm ∘ N
  obtain ⟨hF, hFinj, hFimage, hFpair⟩ :=
    reparametrize_longitudinal_prism hδ.1 hσ hInvP hInjP
  obtain ⟨_, hNimage, hNleft, hNright⟩ :=
    longitudinalPrismCoordinates_properties hδ.1 hσ
  have hNmem (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box δ) :
      N x ∈ (Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ :=
    hNimage.subset (mem_image_of_mem _ hx)
  have hdimFE : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    rw [hdim]
    simp [Module.finrank_prod]
  have hboundary : F '' boxBoundary δ =
      H.symm '' frontier ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ) := by
    rw [← hFpair.frontier_eq_of_finrank_eq hdimFE, hFimage,
      hPrismPair.frontier_eq_of_finrank_eq hdimFE]
  refine ⟨H, δ, F, hδ, hsource, htarget, hHe, hInvHe, rfl, hPT, hF, hFinj,
    hFimage, hboundary, hFpair, hboxSource, hforward, ?_, ?_, ?_⟩
  · intro x hx
    exact hInvHeight (N x) (hNmem x hx)
  · intro x hx
    exact hInvPlane (N x) (hNmem x hx)
  · intro j t z ht hz
    cases j
    · change H.symm (N ((t, -δ), z)) = f false ((t, 0), z)
      rw [hNleft]
      exact hInvLateral false t z ht hz
    · change H.symm (N ((t, δ), z)) = f true ((t, 0), z)
      rw [hNright]
      exact hInvLateral true t z ht hz

end Homeomorph
