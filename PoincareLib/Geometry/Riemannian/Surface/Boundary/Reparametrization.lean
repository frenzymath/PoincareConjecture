import PoincareLib.Geometry.Riemannian.Surface.Boundary.Locality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Reparametrizing surface boundary integrals

The velocity in the retained connection transforms by the ordinary derivative
of a real parameter change. Substitution therefore preserves the boundary
turning integral with its oriented endpoints, including decreasing parameters.
This is the edge cancellation step in Lee, *Introduction to Riemannian
Manifolds*, Theorem 9.7, pp. 277-278.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareMT.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

omit [IsManifold (𝓡 2) ∞ S] in
/-- The curve velocity obeys the real chain rule in the retained tangent bundle. -/
theorem mfderiv_curve_reparam {γ : ℝ → S} {φ : ℝ → ℝ} {t c : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t))
    (hφ : HasDerivAt φ c t) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t 1 =
      c • mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) 1 := by
  rw [mfderiv_comp t hγ hφ.differentiableAt.mdifferentiableAt]
  simp only [mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) (fderiv ℝ φ t 1) = _
  rw [hφ.hasFDerivAt.fderiv]
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) ((1 : ℝ) • c) = _
  rw [one_smul]
  rw [← map_smul]
  simp

/-- Reparametrization multiplies the actual covariant turning integrand by
the parameter derivative. No orientation or unit-length hypothesis is needed. -/
theorem turningAlong_curve_reparam
    (D : LeviCivitaData g) (e₁ e₂ T : (x : S) → TangentSpace (𝓡 2) x)
    {γ : ℝ → S} {φ : ℝ → ℝ} {t c : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t))
    (hφ : HasDerivAt φ c t) :
    g.inner (γ (φ t)) (D.connection T (γ (φ t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t 1))
        (-g.inner (γ (φ t)) (T (γ (φ t))) (e₂ (γ (φ t))) • e₁ (γ (φ t)) +
          g.inner (γ (φ t)) (T (γ (φ t))) (e₁ (γ (φ t))) • e₂ (γ (φ t))) =
      c * g.inner (γ (φ t)) (D.connection T (γ (φ t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) 1))
        (-g.inner (γ (φ t)) (T (γ (φ t))) (e₂ (γ (φ t))) • e₁ (γ (φ t)) +
          g.inner (γ (φ t)) (T (γ (φ t))) (e₁ (γ (φ t))) • e₂ (γ (φ t))) := by
  rw [mfderiv_curve_reparam hγ hφ]
  simp only [map_smul, smul_apply, smul_eq_mul]

/-- A smooth ambient velocity extension makes the boundary turning
coefficient continuous along the curve. -/
theorem continuousOn_surfaceTurningForm_comp_curve
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
    {e₁ e₂ T V : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
    (hV : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) U)
    {γ : ℝ → S} {I : Set ℝ} (hγ : ContinuousOn γ I) (hγU : MapsTo γ I U) :
    ContinuousOn (fun t => D.surfaceTurningForm e₁ e₂ T V (γ t)) I :=
  (D.contMDiffOn_surfaceTurningForm hU he₁ he₂ hT hV).continuousOn.comp hγ hγU

/-- Substitution for the retained boundary turning form. The endpoint order
handles both increasing and decreasing smooth parameter changes. -/
theorem integral_surfaceTurningForm_reparam
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
    {e₁ e₂ T V : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
    (hV : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) U)
    {γ : ℝ → S} {φ φ' : ℝ → ℝ} {a b : ℝ}
    (hφ : ∀ t ∈ uIcc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hγ : ∀ s ∈ φ '' uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ s)
    (hγU : MapsTo γ (φ '' uIcc a b) U)
    (hvelocity : ∀ s ∈ φ '' uIcc a b,
      V (γ s) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ s 1) :
    (∫ t in a..b, g.inner (γ (φ t)) (D.connection T (γ (φ t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t 1))
        (-g.inner (γ (φ t)) (T (γ (φ t))) (e₂ (γ (φ t))) • e₁ (γ (φ t)) +
          g.inner (γ (φ t)) (T (γ (φ t))) (e₁ (γ (φ t))) • e₂ (γ (φ t)))) =
      ∫ s in φ a..φ b, D.surfaceTurningForm e₁ e₂ T V (γ s) := by
  have hcont := D.continuousOn_surfaceTurningForm_comp_curve hU he₁ he₂ hT hV
    (fun s hs => (hγ s hs).continuousAt.continuousWithinAt) hγU
  calc
    _ = ∫ t in a..b, φ' t * D.surfaceTurningForm e₁ e₂ T V (γ (φ t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [D.turningAlong_curve_reparam e₁ e₂ T (hγ _ ⟨t, ht, rfl⟩) (hφ t ht)]
      simp only [surfaceTurningForm, hvelocity _ ⟨t, ht, rfl⟩]
    _ = _ := intervalIntegral.integral_deriv_smul_comp' hφ hφ' hcont

/-- Smooth ambient extensions can change on a shared edge, and either choice
of unit tangent has the same turning. -/
theorem surfaceTurningForm_eq_of_eventuallyEq_or_neg_along_curve
    (D : LeviCivitaData g) {γ : ℝ → S} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ t)
    (e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x)
    {T W V : (x : S) → TangentSpace (𝓡 2) x}
    (hT : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% T) (γ t))
    (hW : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% W) (γ t))
    (heq : (∀ᶠ s in 𝓝 t, W (γ s) = T (γ s)) ∨
      (∀ᶠ s in 𝓝 t, W (γ s) = -T (γ s)))
    (hV : V (γ t) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) :
    D.surfaceTurningForm e₁ e₂ W V (γ t) =
      D.surfaceTurningForm e₁ e₂ T V (γ t) := by
  rcases heq with heq | heq
  · exact D.surfaceTurningForm_eq_of_eventuallyEq_along_curve hγ e₁ e₂ hW hT heq hV hV
  · calc
      _ = D.surfaceTurningForm e₁ e₂ (-T) V (γ t) :=
        D.surfaceTurningForm_eq_of_eventuallyEq_along_curve hγ e₁ e₂ hW
          (mdifferentiableAt_neg_section hT) heq hV hV
      _ = _ := D.surfaceTurningForm_neg_field e₁ e₂ T V (γ t) hT

/-- The turning coefficient is linear in the velocity at its base point. -/
theorem surfaceTurningForm_eq_mul_of_direction_eq_smul
    (D : LeviCivitaData g) (e₁ e₂ T V Z : (x : S) → TangentSpace (𝓡 2) x)
    (x : S) {c : ℝ} (hZ : Z x = c • V x) :
    D.surfaceTurningForm e₁ e₂ T Z x = c * D.surfaceTurningForm e₁ e₂ T V x := by
  simp only [surfaceTurningForm, hZ, map_smul, smul_apply, smul_eq_mul]

/-- Along a reparametrized shared edge, arbitrary differentiable extensions
of either tangent sign give the determinant and parameter-derivative factors. -/
theorem surfaceTurningForm_change_along_reparam
    (D : LeviCivitaData g) (e₁ e₂ f₁ f₂ : (x : S) → TangentSpace (𝓡 2) x)
    {T W V Z : (x : S) → TangentSpace (𝓡 2) x}
    {γ : ℝ → S} {φ : ℝ → ℝ} {t c : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t))
    (hφ : HasDerivAt φ c t)
    (hT : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% T) (γ (φ t)))
    (hW : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% W) (γ (φ t)))
    (heq : (∀ᶠ s in 𝓝 t, W (γ (φ s)) = T (γ (φ s))) ∨
      (∀ᶠ s in 𝓝 t, W (γ (φ s)) = -T (γ (φ s))))
    (hV : V (γ (φ t)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) 1)
    (hZ : Z (γ (φ t)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t 1)
    (hu₁ : g.inner (γ (φ t)) (e₁ (γ (φ t))) (e₁ (γ (φ t))) = 1)
    (hu₂ : g.inner (γ (φ t)) (e₂ (γ (φ t))) (e₂ (γ (φ t))) = 1)
    (ho : g.inner (γ (φ t)) (e₁ (γ (φ t))) (e₂ (γ (φ t))) = 0) :
    D.surfaceTurningForm f₁ f₂ W Z (γ (φ t)) =
      (g.inner (γ (φ t)) (f₁ (γ (φ t))) (e₁ (γ (φ t))) *
          g.inner (γ (φ t)) (f₂ (γ (φ t))) (e₂ (γ (φ t))) -
        g.inner (γ (φ t)) (f₁ (γ (φ t))) (e₂ (γ (φ t))) *
          g.inner (γ (φ t)) (f₂ (γ (φ t))) (e₁ (γ (φ t)))) *
        (c * D.surfaceTurningForm e₁ e₂ T V (γ (φ t))) := by
  rw [D.surfaceTurningForm_change_frame e₁ e₂ f₁ f₂ W Z _ hu₁ hu₂ ho]
  congr 1
  have hlocal := D.surfaceTurningForm_eq_of_eventuallyEq_or_neg_along_curve
    (hγ.comp t hφ.differentiableAt.mdifferentiableAt) e₁ e₂ hT hW heq hZ
  dsimp only [Function.comp_def] at hlocal
  rw [hlocal]
  apply D.surfaceTurningForm_eq_mul_of_direction_eq_smul
  rw [hZ, mfderiv_curve_reparam hγ hφ, hV]

end PoincareMT.LeviCivitaData
