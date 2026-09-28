import PoincareConjecture.Proofs.M14.Sec6_5_HessianIndexComparison










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

private theorem hessian_pair_time_congr {T τ σ : ℝ} (h : τ = σ) (q : G.Point)
    (hq : G.spacetime.timeFunction q = T - τ) (hq' : G.spacetime.timeFunction q = T - σ)
    (f : G.Point → ℝ) (Y : G.Horizontal q) :
    M14ReducedLengthHessianPairing G ⟨q, hq⟩ f Y Y =
      M14ReducedLengthHessianPairing G ⟨q, hq'⟩ f Y Y := by
  subst σ
  rfl




theorem variation_index_eq_hessian_of_action_germ
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hfix : V.left_endpoint_fixed)
    (f : G.Point → ℝ) (O : Set G.Point) (hO : IsOpen O)
    (hp : R.curve (Real.sqrt b) ∈ O)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f O)
    (haction : M14VariationAction V =ᶠ[𝓝 0]
      (fun v => (2 * Real.sqrt b) * f (V.squareFamily (Real.sqrt b) v)))
    (hdf : ∀ W : G.Horizontal (R.curve (Real.sqrt b)),
      mvfderiv (spacetimeModel n) f (R.curve (Real.sqrt b)) W.val =
        G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
          (R.horizontal_velocity (Real.sqrt b)) W / (2 * Real.sqrt b))
    (hq : G.spacetime.timeFunction (R.curve (Real.sqrt b)) = T - b) :
    M14SecondVariationIndexForm V D = (2 * Real.sqrt b) *
      M14ReducedLengthHessianPairing G ⟨R.curve (Real.sqrt b), hq⟩ f
        (M14VariationField V (Real.sqrt b)) (M14VariationField V (Real.sqrt b)) := by
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hc : 2 * Real.sqrt b ≠ 0 := (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).ne'
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hsecond := haction.deriv.deriv_eq
  simp only [deriv_const_mul_field', deriv_const_mul_field] at hsecond
  have hchain := variationEndpoint_secondDeriv_comp
    (hM12.coordinate_gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise)
    V D hs f O hO hp hf
  rw [hessian_pair_time_congr (Real.sq_sqrt hb.le) _ _ hq f _, hdf] at hchain
  obtain ⟨_, d, hd, heq⟩ := secondVariationIdentity_of_squareEuler hCoordinates hM04 hM12 V D
    (fun _ hs W => squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hmin
      D.base_extension hs W)
  rw [hchain, hd.deriv, heq, secondVariationBoundaryTerm_initialFixed V D hfix] at hsecond
  have hcancel := mul_div_cancel₀
    (G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
      (R.horizontal_velocity (Real.sqrt b))
      (M14VariationEndpointAcceleration V D (Real.sqrt b) hs)) hc
  nlinarith

end PoincareConjecture.M14
