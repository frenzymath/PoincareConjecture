import PoincareConjecture.Proofs.M14.Sec6_4_IndexKernelInterior
import PoincareConjecture.Proofs.M14.Mathlib.SectionThroughVector

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem jacobiResidual_eq_zero_of_index_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V)
    (hzero : M14SecondVariationIndexForm V D = 0)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (W : G.Horizontal (R.curve s)) :
    let Q := jacobiFieldDataOfExtension
      (hM12.coordinate_gauges X time I G.spacetime G.slices
        G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
    M14JacobiResidual G R Q s W = 0 := by
  dsimp only
  let Q := jacobiFieldDataOfExtension
    (hM12.coordinate_gauges X time I G.spacetime G.slices
      G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  obtain ⟨Z, hZ, hZs⟩ := FiberBundle.exists_contMDiff_section_through
    (I := spacetimeModel n) (F := EuclideanSpace ℝ (Fin n)) W
  obtain ⟨EZ⟩ := exists_pullbackExtension_Icc (G := G) (γ := R.curve)
    (Y := fun r => Z (R.curve r)) hab
      (hZ.comp_contMDiffOn (R.smooth.mono R.interval_subset))
  have hcont := (jacobiResidual_contDiffOn R Q EZ hM04 hM12).continuousOn
  have hz : EqOn (fun r => M14JacobiResidual G R Q r (Z (R.curve r)))
      (fun _ => 0) (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
    intro r hr
    exact jacobiResidual_eq_zero_of_index_zero_interior hCoordinates hM04 hM12 V D
      hmin hfix hzero hr _
  have hclosed := hz.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (show M14SqrtParameterInterval τ₁ τ₂ ⊆ closure (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) by
      rw [closure_Ioo hab.ne]
      exact Subset.rfl)
  simpa only [hZs] using hclosed hs

theorem variationJacobiCondition_of_index_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V)
    (hzero : M14SecondVariationIndexForm V D = 0) : M14VariationJacobiCondition V D := by
  let Q := jacobiFieldDataOfExtension
    (hM12.coordinate_gauges X time I G.spacetime G.slices
      G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
  obtain ⟨hleft, hright⟩ := variationField_fixed_endpoints_eq_zero V hfix
  exact ⟨Q, rfl, HEq.rfl, hleft, hright, fun _ hs W =>
    jacobiResidual_eq_zero_of_index_zero hCoordinates hM04 hM12 V D hmin hfix hzero hs W⟩

theorem fixedEndpointIndexKernelStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14FixedEndpointIndexKernelStatement G := by
  intro T τ₁ τ₂ x y p R V hmin hfix
  obtain ⟨D⟩ := exists_variationDerivativeData V
  have heuler : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ W : G.Horizontal (R.curve s),
      M14SquareRootEulerResidual G R D.base_extension s W = 0 :=
    fun _ hs W => squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hmin
      D.base_extension hs W
  exact ⟨D, secondVariationIdentity_of_squareEuler hCoordinates hM04 hM12 V D heuler,
    secondVariationBoundaryTerm_eq_zero V D hfix, heuler,
    secondVariationIndexForm_nonneg hCoordinates hM04 hM12 V D hmin hfix,
    variationJacobiCondition_of_index_zero hCoordinates hM04 hM12 V D hmin hfix,
    index_zero_of_variationJacobiCondition hM04 hM12 V D⟩

end PoincareConjecture.M14
