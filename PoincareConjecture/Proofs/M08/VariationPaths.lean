import PoincareConjecture.Proofs.M08.PathBasics
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def variationPath {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    BackwardTimePath F T τ₁ τ₂ := by
  have hmaps : Set.MapsTo (fun τ : ℝ ↦ (Real.sqrt τ, u))
      (Set.Icc τ₁ τ₂) V.squareDomain := by
    intro τ hτ
    exact V.square_contains
      ⟨⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩, hu⟩
  have hagrees (τ : ℝ) (hτ : τ ∈ Set.Icc τ₁ τ₂) :
      V.squareFamily (Real.sqrt τ) u = V.family τ u := by
    have hnonneg : 0 ≤ τ := p.nonnegative.trans hτ.1
    simpa only [Real.sq_sqrt hnonneg] using V.square_agrees (Real.sqrt τ)
      ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩ u hu
  refine {
    curve := fun τ ↦ V.family τ u
    nonnegative := p.nonnegative
    ordered := p.ordered
    terminal_mem := p.terminal_mem
    time_mem := p.time_mem
    continuous := ?_
    regular := ?_
    l_integrable := V.l_integrable u hu }
  · exact (V.square_smooth.continuousOn.comp
      (Real.continuous_sqrt.prodMk continuous_const).continuousOn hmaps).congr
        (fun τ hτ ↦ (hagrees τ hτ).symm)
  · have hsqrt : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1 Real.sqrt
        (Set.Ioo τ₁ τ₂) := by
      intro τ hτ
      exact (Real.contDiffAt_sqrt
        (ne_of_gt (lt_of_le_of_lt p.nonnegative hτ.1))).contMDiffAt.contMDiffWithinAt
    exact ((V.square_smooth.of_le (by simp)).comp
      (hsqrt.prodMk contMDiffOn_const) (hmaps.mono_left Set.Ioo_subset_Icc_self)).congr
        (fun τ hτ ↦ (hagrees τ (Set.Ioo_subset_Icc_self hτ)).symm)

theorem isLocalMin_variationLLength {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) :
    IsLocalMin (variationLLength V.toLVariation) 0 := by
  have hzero : variationLLength V.toLVariation 0 = backwardLLength F T τ₁ τ₂ p.curve := by
    have hcurve : (fun τ ↦ V.family τ 0) = p.curve := funext V.at_zero
    simp only [variationLLength, hcurve]
  change ∀ᶠ u in 𝓝 (0 : ℝ),
    variationLLength V.toLVariation 0 ≤ variationLLength V.toLVariation u
  refine Filter.eventually_of_mem
    (isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩) ?_
  intro u hu
  rw [hzero]
  exact hmin (variationPath V.toLVariation hu) (V.fixed_left u hu) (V.fixed_right u hu)

theorem hasDerivAt_variationLLength_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) {d : ℝ}
    (hd : HasDerivAt (variationLLength V.toLVariation) d 0) : d = 0 :=
  (isLocalMin_variationLLength hmin V).hasDerivAt_eq_zero hd

theorem deriv_variationLLength_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) :
    deriv (variationLLength V.toLVariation) 0 = 0 :=
  (isLocalMin_variationLLength hmin V).deriv_eq_zero

end PoincareConjecture.M08
