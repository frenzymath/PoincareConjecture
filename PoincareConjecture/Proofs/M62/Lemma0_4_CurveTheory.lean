import PoincareConjecture.Proofs.M62.Lemma0_4_RegularizedTotal
import PoincareConjecture.Proofs.M62.Lemma0_4_TotalCurvature
import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeIdentities










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem curve_estimates [T2Space M]
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    M62CurveEstimates F c K0 K1 K2 := by
  have hL := length_continuous F c hc
  have hT := total_curvature_continuous F c hc
  have hR := fun ε (_ : 0 < ε) => regularized_total_continuous F c hc ε
  have hd := fun ε (hε : 0 < ε) t (ht : t ∈ Set.Ioo a b) =>
    (hasDerivAt_regularizedTotal F c hc hε ht).differentiableAt
  have hb := fun ε (hε : 0 < ε) t (ht : t ∈ Set.Ioo a b) =>
    regularized_total_deriv_le F c hc h0 h1 h2 hBounds hε ht
  have he := fun ε (hε : 0 < ε) t (ht : t ∈ Set.Icc a b) =>
    shrinkingCurve_regularization_error F c hc hε.le ht
  have hi := fun s t (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) =>
    total_curvature_integral_of_regularized_bound F c h0 h1 h2 hL hT hR hd hb he hs ht hst
  exact
    { spatial_squared_bound := fun _ ht x => spatial_squared_bound F c hc h0 h1 h2 hBounds ht x
      regularized_positive := fun _ hε t _ x => regularized_pos F c hε t x
      regularized_smooth := fun _ hε =>
        regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)
      regularized_gradient := fun _ hε _ ht x => regularized_gradient_le F c hc hε ht x
      regularized_bound := fun _ hε _ ht x => regularized_deriv_le F c hc h0 h1 h2 hBounds hε ht x
      length_integrable := fun _ ht => length_integrable F c hc ht
      total_curvature_integrable := fun _ ht => total_curvature_integrable F c hc ht
      regularized_integrable := fun ε _ _ ht => regularized_integrable F c hc ε ht
      length_continuous := hL
      total_curvature_continuous := hT
      regularized_continuous := hR
      length_derivative := fun _ ht => hasDerivAt_length F c hc ht
      length_bound := fun _ ht => length_deriv_le_integral F c hc hBounds ht
      length_scalar_bound := fun _ ht => length_deriv_le F c hc hBounds ht
      regularized_differentiable := hd
      regularized_total_bound := hb
      regularization_error := he
      total_curvature_integral := hi
      total_curvature_forward := fun _ ht _ hε =>
        total_curvature_forward_of_integral_bound F c hL hT hi ht hε }



theorem nonempty_curveTheory [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) : Nonempty (M62CurveTheory F) := by
  obtain ⟨G, hG⟩ := exists_spacetimeData F
  exact ⟨
    { spacetime := G
      spacetime_identities := hG
      curves := fun c hc => G.curve_laws c hc
      estimates := fun _ _ _ h0 h1 h2 hb c hc =>
        ⟨curve_estimates F c hc h0 h1 h2 hb, G.curvature_squared_bound c hc h0 h1 h2 hb⟩ }⟩

end PoincareConjecture.M62
