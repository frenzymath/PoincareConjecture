import PoincareConjecture.Proofs.M14.Sec6_4_SecondVariationDensity
import PoincareConjecture.Proofs.M14.Sec6_2_EulerEquation
import PoincareConjecture.Proofs.M14.Sec6_2_SquareEuler
import PoincareConjecture.Proofs.M14.Sec6_4_IndexPositivity











set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}




theorem secondVariationIdentity_of_squareEuler
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (heuler : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ Z : G.Horizontal (R.curve s),
      M14SquareRootEulerResidual G R D.base_extension s Z = 0) :
    M14SecondVariationIdentity V D := by
  refine ⟨⟨_, firstVariationIdentity hCoordinates hM12 V D, rfl⟩, ?_⟩
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  let C := M14SqrtParameterInterval τ₁ τ₂
  let raw := fun s => M08.variationParameterDeriv C V.parameterDomain
    (M08.variationParameterDeriv C V.parameterDomain (variationActionDensity V)) (s, 0)
  let B := variationAccelerationBoundaryPair V D
  let dB := derivWithin B C
  let Idx := M14SecondVariationIndexDensity V D
  have hab : a < b := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hab
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hraw : ContinuousOn raw C :=
    (M08.variationParameterDeriv_contDiffOn hC hP _
      (M08.variationParameterDeriv_contDiffOn hC hP _
        (variationActionDensity_contDiffOn hM12 V))).continuousOn.comp
      (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hzero⟩)
  have hB : ContDiffOn ℝ ∞ B C := variationAccelerationBoundaryPair_contDiffOn V D
    (hM12.coordinate_gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise)
  have hdB : ContinuousOn dB C := (hB.derivWithin hC (m := ∞) (by simp)).continuousOn
  have hrawInt : IntervalIntegrable raw volume a b := hraw.intervalIntegrable_of_Icc hab.le
  have hdBInt : IntervalIntegrable dB volume a b := hdB.intervalIntegrable_of_Icc hab.le
  have hid (s : ℝ) (hs : s ∈ Ioo a b) : raw s = dB s + Idx s := by
    have h := secondVariation_density_identity_with_residual hM04 hM12 V D hs
    rw [heuler s (Ioo_subset_Icc_self hs), sub_zero] at h
    exact h
  have hIdxInt : IntervalIntegrable Idx volume a b := by
    apply (hrawInt.sub hdBInt).congr_uIoo
    intro s hs
    rw [uIoo_of_le hab.le] at hs
    have h := hid s hs
    linarith
  have hFTC : (∫ s in a..b, dB s) = B b - B a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hB.continuousOn
      (fun s hs => (((hB s (Ioo_subset_Icc_self hs)).differentiableWithinAt
        (by simp)).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds hs.1 hs.2)) hdBInt
  have hvalue : (∫ s in a..b, raw s) =
      M14SecondVariationBoundaryTerm V D + M14SecondVariationIndexForm V D := by
    calc
      (∫ s in a..b, raw s) = ∫ s in a..b, dB s + Idx s :=
        intervalIntegral.integral_congr_Ioo_of_le hab.le hid
      _ = (∫ s in a..b, dB s) + ∫ s in a..b, Idx s :=
        intervalIntegral.integral_add hdBInt hIdxInt
      _ = _ := by
        rw [hFTC, secondVariationBoundaryTerm_eq_accelerationPair V D]
        rfl
  refine ⟨_, ?_, rfl⟩
  have h := hasDerivAt_deriv_variationAction_integral hM12 V hzero
  change HasDerivAt (fun u => deriv (M14VariationAction V) u) (∫ s in a..b, raw s) 0 at h
  rwa [hvalue] at h




theorem secondVariationIdentity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (E₀ : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E₀) : M14SecondVariationIdentity V D :=
  secondVariationIdentity_of_squareEuler hCoordinates hM04 hM12 V D
    (fun _ hs Z => squareRootEulerResidual_eq_zero_of_euler p hCoordinates hM12 E₀ heuler R
      D.base_extension hs Z)




theorem secondVariationStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14SecondVariationStatement G := by
  intro T τ₁ τ₂ x y p R V E₀ heuler
  obtain ⟨D⟩ := exists_variationDerivativeData V
  exact ⟨D, secondVariationIdentity hCoordinates hM04 hM12 V D E₀ heuler⟩




theorem secondVariationIndexForm_nonneg
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V) :
    0 ≤ M14SecondVariationIndexForm V D :=
  secondVariationIndexForm_nonneg_of_identity V D hmin hfix
    (secondVariationIdentity_of_squareEuler hCoordinates hM04 hM12 V D
      (fun _ hs Z => squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hmin
        D.base_extension hs Z))




theorem fixedEndpointIndexStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14FixedEndpointIndexStatement G := by
  intro T τ₁ τ₂ x y p R V hmin hfix
  obtain ⟨D⟩ := exists_variationDerivativeData V
  refine ⟨D, fun _ hs Z => squareRootEulerResidual_eq_zero_of_minimizing
    hCoordinates hM12 hmin D.base_extension hs Z, ?_⟩
  exact secondVariationIndexForm_nonneg hCoordinates hM04 hM12 V D hmin hfix

end PoincareConjecture.M14
