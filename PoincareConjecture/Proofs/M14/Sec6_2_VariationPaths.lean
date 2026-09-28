import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence
import PoincareConjecture.Statements.M14PathCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}



def variationPath (V : M14LVariationData G p R) {u : ℝ} (hu : u ∈ V.parameterDomain)
    (hx : V.family τ₁ u = x) (hy : V.family τ₂ u = y) :
    M14BackwardPath G T τ₁ τ₂ x y := by
  have hmaps : Set.MapsTo (fun τ : ℝ => (Real.sqrt τ, u))
      (Set.Icc τ₁ τ₂) V.squareDomain := by
    intro τ hτ
    exact V.square_contains ⟨⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩, hu⟩
  have hagrees (τ : ℝ) (hτ : τ ∈ Set.Icc τ₁ τ₂) :
      V.squareFamily (Real.sqrt τ) u = V.family τ u := by
    simpa only [Real.sq_sqrt (p.tau_nonneg.trans hτ.1)] using V.square_agrees (Real.sqrt τ)
      ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩ u hu
  refine {
    tau_nonneg := p.tau_nonneg
    tau_lt := p.tau_lt
    base_time := p.base_time
    endpoint_time := p.endpoint_time
    curve := fun τ => V.family τ u
    curve_start := hx
    curve_end := hy
    curve_time := V.family_time u hu
    curve_continuous := ?_
    curve_regular := ?_
    horizontal_velocity := V.family_velocity u
    derivative_eq := V.family_derivative u hu
    action_integrable := V.action_integrable u hu }
  · exact (V.square_smooth.continuousOn.comp
      (Real.continuous_sqrt.prodMk continuous_const).continuousOn hmaps).congr
        (fun τ hτ => (hagrees τ hτ).symm)
  · have hsqrt : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1 Real.sqrt (Set.Ioo τ₁ τ₂) := by
      intro τ hτ
      exact (Real.contDiffAt_sqrt
        (ne_of_gt (p.tau_nonneg.trans_lt hτ.1))).contMDiffAt.contMDiffWithinAt
    exact ((V.square_smooth.of_le (by simp)).comp
      (hsqrt.prodMk contMDiffOn_const) (hmaps.mono_left Set.Ioo_subset_Icc_self)).congr
        (fun τ hτ => (hagrees τ (Set.Ioo_subset_Icc_self hτ)).symm)



theorem variationAction_zero (V : M14LVariationData G p R) :
    M14VariationAction V 0 = M14BackwardLAction G p := by
  have hz : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  let q := variationPath V hz ((V.family_at_zero τ₁).trans p.curve_start)
    ((V.family_at_zero τ₂).trans p.curve_end)
  exact action_eq_of_curve_eqOn q p (fun τ _ => V.family_at_zero τ)



theorem isLocalMin_variationAction (V : M14LVariationData G p R)
    (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V) :
    IsLocalMin (M14VariationAction V) 0 := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hz : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  apply Filter.eventually_of_mem (hP.mem_nhds hz)
  intro u hu
  change M14VariationAction V 0 ≤ M14VariationAction V u
  rw [variationAction_zero V]
  exact hmin (variationPath V hu
    (((V.left_endpoint_fixed_spec.mp hfix.1) u hu).trans p.curve_start)
    (((V.right_endpoint_fixed_spec.mp hfix.2) u hu).trans p.curve_end))



theorem hasDerivAt_variationAction_eq_zero (V : M14LVariationData G p R)
    (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V)
    {d : ℝ} (hd : HasDerivAt (M14VariationAction V) d 0) : d = 0 :=
  (isLocalMin_variationAction V hmin hfix).hasDerivAt_eq_zero hd

end PoincareConjecture.M14
