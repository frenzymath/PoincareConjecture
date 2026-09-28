import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.SquareTime








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle
universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}

set_option maxHeartbeats 1500000 in
theorem variationBaseField_pullback_chart (V : LVariation F T τ₁ τ₂ p)
    (x : M) (W : ℝ × ℝ → EuclideanSpace ℝ (Fin n))
    (hW : ContDiffOn ℝ ∞ W (variationChartDomain V x))
    (Y : ∀ s, TangentSpace (𝓡 n) (V.baseSquareCurve s))
    (hfield : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source →
      chartFrame x (W (s, 0)) (V.baseSquareCurve s) = Y s)
    (E : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) V.baseSquareCurve Y)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve Y
        (sqrtParameterInterval τ₁ τ₂) E s =
      chartFrame x (coordinatePartialS W (s, 0) +
        Frame.chartConnection (chartActionMetric F T x)
          (s, variationChart V x (s, 0))
          (coordinatePartialS (variationChart V x) (s, 0)) (W (s, 0))) (V.baseSquareCurve s) := by
  let C := sqrtParameterInterval τ₁ τ₂
  let Ω := variationChartDomain V x
  let N := (fun r : ℝ ↦ (r, (0 : ℝ))) ⁻¹' Ω
  let c := fun r : ℝ ↦ W (r, 0)
  have hΩ : IsOpen Ω := variationChartDomain_open V x
  have hN : IsOpen N := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hsN : s ∈ N := ⟨V.square_contains ⟨hs, hzero⟩, hx⟩
  have hc : ContDiffOn ℝ ∞ c N :=
    hW.comp (contDiffOn_id.prodMk contDiffOn_const) (fun r hr ↦ hr)
  have hsrc : MapsTo V.baseSquareCurve (C ∩ N)
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source := fun r hr ↦ hr.2.2
  have hrepr (r : ℝ) (hr : r ∈ C ∩ N) :
      chartFrame x (c r) (V.baseSquareCurve r) = Y r := hfield r hr.1 (hsrc hr)
  have hpb := pullbackCovariantDerivative_chart_formula_local F (fun r ↦ T - r ^ 2)
    hN x V.baseSquareCurve c hc hsrc Y hrepr E hs hsN
      (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered) s hs)
      (variationBaseSquare_mdifferentiableAt V hs)
  have hdc := (coordinateSlice_fst_hasDerivAt W
    (((hW (s, 0) hsN).contDiffAt (hΩ.mem_nhds hsN)).differentiableAt (by simp))).deriv
  have hdq := (coordinateSlice_fst_hasDerivAt (variationChart V x)
    ((((variationChart_contDiffOn V x) (s, 0) hsN).contDiffAt
      (hΩ.mem_nhds hsN)).differentiableAt (by simp))).deriv
  change deriv c s = coordinatePartialS W (s, 0) at hdc
  change deriv ((extChartAt (𝓡 n) x) ∘ V.baseSquareCurve) s =
    coordinatePartialS (variationChart V x) (s, 0) at hdq
  rw [hpb, hdc, hdq, Frame.chartConnection_eq_retainedConnection_squareDomain F T s x _ hx ht]
  exact ((trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x).symmL ℝ (V.baseSquareCurve s)).map_add _ _ |>.symm

theorem variationCovariantField_chart (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) {x : M} {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
        (squareVariationField V) (sqrtParameterInterval τ₁ τ₂) D.variation_extension s =
      chartFrame x (coordinatePartialS (coordinatePartialU (variationChart V x)) (s, 0) +
        Frame.chartConnection (chartActionMetric F T x)
          (s, variationChart V x (s, 0))
          (coordinatePartialS (variationChart V x) (s, 0))
          (coordinatePartialU (variationChart V x) (s, 0))) (V.baseSquareCurve s) :=
  variationBaseField_pullback_chart V x _
    (coordinatePartialU_contDiffOn (variationChartDomain_open V x) _ (variationChart_contDiffOn V x))
    _ (fun r hr hx ↦ variationChart_squareVariationField V hr hx) D.variation_extension hs hx ht

theorem variationCovariantVelocity_chart (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) {x : M} {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
        (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂))
        (sqrtParameterInterval τ₁ τ₂) D.velocity_extension s =
      chartFrame x (coordinatePartialS (coordinatePartialS (variationChart V x)) (s, 0) +
        Frame.chartConnection (chartActionMetric F T x)
          (s, variationChart V x (s, 0))
          (coordinatePartialS (variationChart V x) (s, 0))
          (coordinatePartialS (variationChart V x) (s, 0))) (V.baseSquareCurve s) :=
  variationBaseField_pullback_chart V x _
    (coordinatePartialS_contDiffOn (variationChartDomain_open V x) _ (variationChart_contDiffOn V x))
    _ (fun r hr hx ↦ variationChart_baseVelocity V hr hx) D.velocity_extension hs hx ht


end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
