import PoincareConjecture.Proofs.M14.Sec6_5_VariationHessianChain
import PoincareConjecture.Proofs.M14.Sec6_5_VariationContact
import PoincareConjecture.Proofs.M14.Sec6_4_RealizedIndex
import PoincareConjecture.Proofs.M09.SecondDerivativeComparison

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

theorem initialFixed_squareEndpoint_constant (V : M14LVariationData G p R)
    (hfix : V.left_endpoint_fixed) :
    EqOn (V.squareFamily (Real.sqrt a)) (fun _ => V.squareFamily (Real.sqrt a) 0)
      V.parameterDomain := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hpoint (v : ℝ) (hv : v ∈ V.parameterDomain) :
      V.squareFamily (Real.sqrt a) v = p.curve a := by
    rw [V.square_agrees _ ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩ v hv,
      Real.sq_sqrt p.tau_nonneg]
    exact (V.left_endpoint_fixed_spec.mp hfix) v hv
  exact fun v hv => (hpoint v hv).trans (hpoint 0 hzero).symm

theorem secondVariationBoundaryTerm_initialFixed (V : M14LVariationData G p R)
    (D : M14VariationDerivativeData V) (hfix : V.left_endpoint_fixed) :
    M14SecondVariationBoundaryTerm V D =
      G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
        (R.horizontal_velocity (Real.sqrt b))
        (M14VariationEndpointAcceleration V D (Real.sqrt b)
          ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩) := by
  have hleft := variationEndpointAcceleration_eq_zero_of_constant V D
    ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩ (initialFixed_squareEndpoint_constant V hfix)
  simp only [M14SecondVariationBoundaryTerm, hleft, map_zero, sub_zero, M14SquareRootVelocity]

private theorem hessian_pair_time_congr {T τ σ : ℝ} (h : τ = σ) (q : G.Point)
    (hq : G.spacetime.timeFunction q = T - τ) (hq' : G.spacetime.timeFunction q = T - σ)
    (f : G.Point → ℝ) (Y : G.Horizontal q) :
    M14ReducedLengthHessianPairing G ⟨q, hq⟩ f Y Y =
      M14ReducedLengthHessianPairing G ⟨q, hq'⟩ f Y Y := by
  subst σ
  rfl

theorem variation_hessian_le_index
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hfix : V.left_endpoint_fixed)
    (f : G.Point → ℝ) (O : Set G.Point) (hO : IsOpen O)
    (hp : R.curve (Real.sqrt b) ∈ O)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hgap : IsLocalMin (fun v => M14VariationAction V v -
      (2 * Real.sqrt b) * f (V.squareFamily (Real.sqrt b) v)) 0)
    (hdf : ∀ W : G.Horizontal (R.curve (Real.sqrt b)),
      mvfderiv (spacetimeModel n) f (R.curve (Real.sqrt b)) W.val =
        G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
          (R.horizontal_velocity (Real.sqrt b)) W / (2 * Real.sqrt b))
    (hq : G.spacetime.timeFunction (R.curve (Real.sqrt b)) = T - b) :
    M14ReducedLengthHessianPairing G ⟨R.curve (Real.sqrt b), hq⟩ f
      (M14VariationField V (Real.sqrt b)) (M14VariationField V (Real.sqrt b)) ≤
        M14SecondVariationIndexForm V D / (2 * Real.sqrt b) := by
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hc : 0 < 2 * Real.sqrt b := mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hS := (variationAction_contDiffOn hM12 V).contDiffAt (hP.mem_nhds hzero)
  have hg : ContDiffAt ℝ ∞ (fun v => f (V.squareFamily (Real.sqrt b) v)) 0 := by
    apply ContMDiffAt.contDiffAt
    apply (hf.contMDiffAt (hO.mem_nhds (V.square_base (Real.sqrt b) ▸ hp))).comp
    exact (variationEndpoint_contMDiffOn V hs).contMDiffAt (hP.mem_nhds hzero)
  have hsecond := Proofs.M09.localMin_secondDeriv_scaled_comparison
    (M14VariationAction V) (fun v => f (V.squareFamily (Real.sqrt b) v))
      (2 * Real.sqrt b) 0 hS hg hgap
  have hchain := variationEndpoint_secondDeriv_comp
    (hM12.coordinate_gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise)
    V D hs f O hO hp hf
  rw [hessian_pair_time_congr (Real.sq_sqrt hb.le) _ _ hq f _, hdf] at hchain
  obtain ⟨_, d, hd, heq⟩ := secondVariationIdentity_of_squareEuler hCoordinates hM04 hM12 V D
    (fun _ hs W => squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hmin
      D.base_extension hs W)
  rw [hchain, hd.deriv, heq, secondVariationBoundaryTerm_initialFixed V D hfix] at hsecond
  apply (le_div_iff₀ hc).mpr
  have hcancel := mul_div_cancel₀
    (G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
      (R.horizontal_velocity (Real.sqrt b))
      (M14VariationEndpointAcceleration V D (Real.sqrt b) hs)) hc.ne'
  nlinarith

theorem hessian_le_pullback_index
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hmin : M14IsMinimizing p) (f : G.Point → ℝ) (O : Set G.Point) (hO : IsOpen O)
    (hp : R.curve (Real.sqrt b) ∈ O)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hvalue : f (R.curve (Real.sqrt b)) = M14BackwardLAction G p / (2 * Real.sqrt b))
    (hcontact : ∀ᶠ q in 𝓝 (R.curve (Real.sqrt b)), f q ≤ M14ReducedLengthAt G T a x q)
    (hfinite : ∀ᶠ q in 𝓝 (R.curve (Real.sqrt b)),
      M14FiniteValueDomain G T a (T - G.spacetime.timeFunction q) x q)
    (hdf : ∀ W : G.Horizontal (R.curve (Real.sqrt b)),
      mvfderiv (spacetimeModel n) f (R.curve (Real.sqrt b)) W.val =
        G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
          (R.horizontal_velocity (Real.sqrt b)) W / (2 * Real.sqrt b))
    (hq : G.spacetime.timeFunction (R.curve (Real.sqrt b)) = T - b)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (hleft : Y (Real.sqrt a) = 0) :
    M14ReducedLengthHessianPairing G ⟨R.curve (Real.sqrt b), hq⟩ f
        (Y (Real.sqrt b)) (Y (Real.sqrt b)) ≤
      (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EY s) /
        (2 * Real.sqrt b) := by
  have hY := pullbackExtension_field_contMDiffOn EY (R.smooth.mono R.interval_subset)
  obtain ⟨V, hfix, hfield, _⟩ :=
    exists_initialFixed_variation_of_smooth_horizontalField R hM12 Y hY hleft
  obtain ⟨D⟩ := exists_variationDerivativeData V
  have hgap := isLocalMin_variationAction_gap hM12 V hfix f hvalue hcontact hfinite
  have h := variation_hessian_le_index hCoordinates hM04 hM12 V D hmin hfix f O hO hp hf hgap hdf hq
  rwa [secondVariationIndexForm_eq_of_field V D EY hfield,
    hfield _ ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩] at h

end PoincareConjecture.M14
