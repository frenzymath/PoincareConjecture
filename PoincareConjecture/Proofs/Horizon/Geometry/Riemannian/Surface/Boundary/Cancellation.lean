import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Normalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

section PairedEdges

variable (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
  {e₁ e₂ f₁ f₂ T W V Z : (x : S) → TangentSpace (𝓡 2) x}
  (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
  (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
  (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
  (hV : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) U)
  (hu₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
  (hu₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
  (ho : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
  {γ : ℝ → S} {φ φ' : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
  (hφ : ∀ t ∈ uIcc a b, HasDerivAt φ (φ' t) t)
  (hφ' : ContinuousOn φ' (uIcc a b))
  (hγ : ∀ s ∈ φ '' uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ s)
  (hγU : MapsTo γ (φ '' uIcc a b) U)
  (hW : ∀ t ∈ Ioo a b,
    MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% W) (γ (φ t)))
  (heq : ∀ t ∈ Ioo a b,
    (∀ᶠ s in 𝓝 t, W (γ (φ s)) = T (γ (φ s))) ∨
      (∀ᶠ s in 𝓝 t, W (γ (φ s)) = -T (γ (φ s))))
  (hvelocity : ∀ t ∈ Ioo a b,
    V (γ (φ t)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) 1)
  (hZ : ∀ t ∈ Ioo a b,
    Z (γ (φ t)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t 1)
  (hdet : ∀ t ∈ Ioo a b,
    g.inner (γ (φ t)) (f₁ (γ (φ t))) (e₁ (γ (φ t))) *
        g.inner (γ (φ t)) (f₂ (γ (φ t))) (e₂ (γ (φ t))) -
      g.inner (γ (φ t)) (f₁ (γ (φ t))) (e₂ (γ (φ t))) *
        g.inner (γ (φ t)) (f₂ (γ (φ t))) (e₁ (γ (φ t))) = δ)

include hU he₁ he₂ hT hV hu₁ hu₂ ho hab hφ hφ' hγ hγU hW heq hvelocity hZ hdet

theorem integral_surfaceTurningForm_change_reparam :
    (∫ t in a..b, D.surfaceTurningForm f₁ f₂ W Z (γ (φ t))) =
      δ * ∫ s in φ a..φ b, D.surfaceTurningForm e₁ e₂ T V (γ s) := by
  have hcont := D.continuousOn_surfaceTurningForm_comp_curve hU he₁ he₂ hT hV
    (fun s hs => (hγ s hs).continuousAt.continuousWithinAt) hγU
  calc
    _ = ∫ t in a..b, δ * (φ' t * D.surfaceTurningForm e₁ e₂ T V (γ (φ t))) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      dsimp only
      have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self ht
      have himg : φ t ∈ φ '' uIcc a b := ⟨t, ht', rfl⟩
      have hx := hγU himg
      rw [D.surfaceTurningForm_change_along_reparam e₁ e₂ f₁ f₂ (hγ _ himg)
        (hφ t ht') ((hT.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
        (hW t ht) (heq t ht) (hvelocity t ht) (hZ t ht) (hu₁ _ hx) (hu₂ _ hx) (ho _ hx),
        hdet t ht]
    _ = δ * ∫ t in a..b, φ' t * D.surfaceTurningForm e₁ e₂ T V (γ (φ t)) :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := congrArg (δ * ·) (intervalIntegral.integral_deriv_smul_comp' hφ hφ' hcont)

theorem integral_surfaceTurningForm_pair_eq_zero {c d : ℝ}
    (hendpoints : (δ = -1 ∧ φ a = c ∧ φ b = d) ∨
      (δ = 1 ∧ φ a = d ∧ φ b = c)) :
    (∫ t in a..b, D.surfaceTurningForm f₁ f₂ W Z (γ (φ t))) +
      (∫ s in c..d, D.surfaceTurningForm e₁ e₂ T V (γ s)) = 0 := by
  rw [D.integral_surfaceTurningForm_change_reparam hU he₁ he₂ hT hV hu₁ hu₂ ho
    hab hφ hφ' hγ hγU hW heq hvelocity hZ hdet]
  rcases hendpoints with ⟨rfl, ha, hb⟩ | ⟨rfl, ha, hb⟩
  · rw [ha, hb, neg_one_mul, neg_add_cancel]
  · rw [ha, hb, one_mul, intervalIntegral.integral_symm d c, add_neg_cancel]

omit heq in

theorem integral_normalized_surfaceTurningForm_pair_eq_zero {c d : ℝ}
    (hregular : ∀ t ∈ Ioo a b, Z (γ (φ t)) ≠ 0)
    (hTnorm : ∀ t ∈ Ioo a b, T (γ (φ t)) =
      (Real.sqrt (g.inner (γ (φ t)) (V (γ (φ t))) (V (γ (φ t)))))⁻¹ • V (γ (φ t)))
    (hWnorm : ∀ t ∈ Ioo a b, W (γ (φ t)) =
      (Real.sqrt (g.inner (γ (φ t)) (Z (γ (φ t))) (Z (γ (φ t)))))⁻¹ • Z (γ (φ t)))
    (hendpoints : (δ = -1 ∧ φ a = c ∧ φ b = d) ∨
      (δ = 1 ∧ φ a = d ∧ φ b = c)) :
    (∫ t in a..b, D.surfaceTurningForm f₁ f₂ W Z (γ (φ t))) +
      (∫ s in c..d, D.surfaceTurningForm e₁ e₂ T V (γ s)) = 0 := by
  have hsub : Ioo a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab]
    exact Ioo_subset_Icc_self
  have hlocal (t : ℝ) (ht : t ∈ Ioo a b) :=
    normalized_fields_eventuallyEq_or_neg_along_reparam isOpen_Ioo
    (fun t ht => hφ t (hsub ht)) (hφ'.mono hsub)
      (fun t ht => hγ _ ⟨t, hsub ht, rfl⟩) hvelocity hZ hregular hTnorm hWnorm ht
  exact D.integral_surfaceTurningForm_pair_eq_zero hU he₁ he₂ hT hV hu₁ hu₂ ho
    hab hφ hφ' hγ hγU hW hlocal hvelocity hZ hdet hendpoints

end PairedEdges

end PoincareConjecture.LeviCivitaData
