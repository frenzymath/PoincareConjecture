import PoincareConjecture.Proofs.M76.Mathlib.RetainedLongitudinalPrism
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior













set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]








theorem IsFinitePL.exists_interior_chart_with_fixed_lateral_prism
    {S surface : Set E} {T : Set ((ℝ × ℝ) × ℝ)} {e : S ≃ₜ T}
    (he : e.IsFinitePL) (hdim : Module.finrank ℝ E = 3)
    (A : E → ℝ) (hheight : ∀ x : S, (e x : (ℝ × ℝ) × ℝ).1.1 = A x)
    (hplane : ∀ x : S, (e x : (ℝ × ℝ) × ℝ).2 = 0 ↔ (x : E) ∈ surface)
    (σ : Bool → ℝ) (hσ : σ false < σ true)
    (haxis : ∀ s ∈ Icc (σ false) (σ true), ((0, s), 0) ∈ interior T)
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    {r : ℝ} (hr : 0 < r) (hbox : ∀ j, f j '' box r ⊆ interior S)
    (hkeep : ∀ j (x : S), (x : E) ∈ f j '' box r → (e x : (ℝ × ℝ) × ℝ) = L j x)
    (hlateral : ∀ j t z, L j (f j ((t, 0), z)) = ((t, σ j), z)) :
    ∃ (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ)) (δ : ℝ),
      δ ∈ Ioo 0 r ∧ H.source = interior S ∧ H.target = interior T ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      FinitePiecewiseAffineOn (H : E → (ℝ × ℝ) × ℝ) S ∧
      FinitePiecewiseAffineOn (H.symm : ((ℝ × ℝ) × ℝ) → E) T ∧
      (∀ x : S, H x = (e x : (ℝ × ℝ) × ℝ)) ∧
      (∀ y : T, H.symm y = (e.symm y : E)) ∧
      (Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ ⊆ H.target ∧
      FinitePiecewiseAffineOn H.symm
        ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ) ∧
      InjOn H.symm ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (H.symm '' ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ))
        (H.symm '' frontier ((Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ)) ∧
      (∀ j, f j '' box δ ⊆ H.source) ∧
      (∀ j x, x ∈ box δ → H (f j x) = L j (f j x)) ∧
      (∀ y ∈ (Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ,
        A (H.symm y) = y.1.1) ∧
      (∀ y ∈ (Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ,
        H.symm y ∈ surface ↔ y.2 = 0) ∧
      ∀ j t z, t ∈ Icc (-δ) δ → z ∈ Icc (-δ) δ →
        H.symm ((t, σ j), z) = f j ((t, 0), z) := by
  have hdimF : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  obtain ⟨H, hsource, htarget, hH, hInvH, hfinite, hInvFinite, hHe, hInvHe⟩ :=
    he.exists_interior_chart (hdim.trans hdimF.symm)
  obtain ⟨δ, hδ, hprism⟩ := isOpen_interior.exists_longitudinal_prism_subset haxis hr
  let P : Set ((ℝ × ℝ) × ℝ) :=
    (Icc (-δ) δ ×ˢ Icc (σ false) (σ true)) ×ˢ Icc (-δ) δ
  have hPT : P ⊆ H.target := hprism.trans htarget.symm.subset
  have hdelta : -δ < δ := by linarith [hδ.1]
  have hpair := ((isFinitePLBallPair_Icc hdelta).prod
    (isFinitePLBallPair_Icc hσ)).prod (isFinitePLBallPair_Icc hdelta)
  have hpair' := hpair
  rw [← hpair.frontier_eq_of_finrank_eq rfl] at hpair'
  change IsFinitePLBallPair ((ℝ × ℝ) × ℝ) P (frontier P) at hpair'
  have hcopy := hpair'
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hInvP : FinitePiecewiseAffineOn H.symm P := by
    rw [← hKs]
    exact hInvFinite.restrict K hK (hKs.subset.trans (hprism.trans interior_subset))
  have hInjP : InjOn H.symm P := H.symm.injOn.mono hPT
  have hsmall : box δ ⊆ box r := by
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall hδ.2.le
  have hboxSource (j : Bool) : f j '' box δ ⊆ H.source :=
    (image_mono hsmall).trans ((hbox j).trans hsource.symm.subset)
  have hforward (j : Bool) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box δ) :
      H (f j x) = L j (f j x) := by
    have hximage : f j x ∈ f j '' box r := ⟨x, hsmall hx, rfl⟩
    let y : S := ⟨f j x, interior_subset (hbox j hximage)⟩
    exact (hHe y).trans (hkeep j y hximage)
  refine ⟨H, δ, hδ, hsource, htarget, hH, hInvH, hfinite, hInvFinite, hHe, hInvHe,
    hPT, hInvP, hInjP, hpair'.image hInvP hInjP, hboxSource, hforward, ?_, ?_, ?_⟩
  · intro y hy
    have hyT : y ∈ T := interior_subset (hprism hy)
    rw [hInvHe ⟨y, hyT⟩]
    simpa only [e.apply_symm_apply] using (hheight (e.symm ⟨y, hyT⟩)).symm
  · intro y hy
    have hyT : y ∈ T := interior_subset (hprism hy)
    rw [hInvHe ⟨y, hyT⟩]
    simpa only [e.apply_symm_apply] using (hplane (e.symm ⟨y, hyT⟩)).symm
  · intro j t z ht hz
    have hxbox : ((t, 0), z) ∈ box δ :=
      ⟨⟨ht, neg_nonpos.mpr hδ.1.le, hδ.1.le⟩, hz⟩
    have hxsource : f j ((t, 0), z) ∈ H.source :=
      hboxSource j ⟨((t, 0), z), hxbox, rfl⟩
    have hvalue : H (f j ((t, 0), z)) = ((t, σ j), z) :=
      (hforward j ((t, 0), z) hxbox).trans (hlateral j t z)
    have hinv := H.left_inv hxsource
    rwa [hvalue] at hinv

end Homeomorph
