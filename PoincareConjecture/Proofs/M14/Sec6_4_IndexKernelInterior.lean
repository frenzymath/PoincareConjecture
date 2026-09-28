import PoincareConjecture.Proofs.M14.Sec6_4_SupportedIndexTest
import PoincareConjecture.Proofs.M14.Mathlib.IntervalTestFunctions










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

variable (hCoordinates : M12MetricPredecessors.{0} n)
  (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
  (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V)
  (hzero : M14SecondVariationIndexForm V D = 0)

include hCoordinates hM04 hM12 hmin hfix hzero




theorem jacobiResidual_supportedGauge_eq_zero
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U)
    (Z : M14LVariationData G p R)
    (hZ : ∀ s v, Z.squareFamily s v = supportedGaugeFamily R b lift η (s, v))
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      (M14VariationField Z)) :
    let Q := jacobiFieldDataOfExtension
      (hM12.coordinate_gauges X time I G.spacetime G.slices
        G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
    ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      M14JacobiResidual G R Q s (M14VariationField Z s) = 0 := by
  dsimp only
  let Q := jacobiFieldDataOfExtension
    (hM12.coordinate_gauges X time I G.spacetime G.slices
      G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hcont := (jacobiResidual_contDiffOn R Q EZ hM04 hM12).continuousOn
  apply hcont.eq_zero_of_intervalIntegral_contDiff_smul hab
  intro ψ hψ _ _
  let ξ := fun s => ψ s • η s
  have hξ : ContDiff ℝ ∞ ξ := hψ.smul hη
  have hξη : tsupport ξ ⊆ tsupport η := tsupport_smul_subset_right ψ η
  obtain ⟨Zξ, hfixξ, hZξ⟩ := exists_supportedGauge_variation R b lift ξ hM12 hU hlift
    hright hξ (hξη.trans hsupport) (fun s hs => hsrc s (hξη hs))
  obtain ⟨Dξ⟩ := exists_variationDerivativeData Zξ
  have hfield (s : ℝ) (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
      M14VariationField Zξ s = ψ s • M14VariationField Z s := by
    apply Subtype.ext
    have hξval := variationField_supportedGauge_val R b lift ξ Zξ hZξ
      (fun t ht => hright _ (hsrc t (hξη ht))) hs
    have hηval := variationField_supportedGauge_val R b lift η Z hZ
      (fun t ht => hright _ (hsrc t ht)) hs
    have hlinear := congrArg Subtype.val (((G.gaugeCover.metric b).spatialTangentEquiv
      (lift (R.curve s)).1 (lift (R.curve s)).2).map_smul (ψ s) (η s))
    exact hξval.trans (hlinear.trans
      (congrArg (fun w : SpacetimeModelVector n => ψ s • w) hηval.symm))
  have hz := jacobiResidual_supportedGauge_integral_eq_zero hCoordinates hM04 hM12 V D
    hmin hfix hzero b lift ξ hU hlift hright hξ (hξη.trans hsupport)
      (fun s hs => hsrc s (hξη hs)) Zξ hZξ Dξ.variation_extension hfixξ
  rw [← hz]
  apply intervalIntegral.integral_congr_Ioo_of_le hab.le
  intro s hs
  change ψ s • M14JacobiResidual G R Q s (M14VariationField Z s) =
    M14JacobiResidual G R Q s (M14VariationField Zξ s)
  rw [hfield s (Ioo_subset_Icc_self hs)]
  exact (horizontalJacobiPairResidual_smul_right R hM04 hM12 (Ioo_subset_Icc_self hs)
    (Q.field s) (M14JacobiFirstDerivative Q s) (M14JacobiSecondDerivative Q s)
      (M14VariationField Z s) (ψ s)).symm




theorem jacobiResidual_eq_zero_of_index_zero_interior
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (W : G.Horizontal (R.curve s)) :
    let Q := jacobiFieldDataOfExtension
      (hM12.coordinate_gauges X time I G.spacetime G.slices
        G.timeIntervals G.gaugeCover G.leafwise) D.variation_extension
    M14JacobiResidual G R Q s W = 0 := by
  obtain ⟨b, U, lift, hU, hlift, hright, η, hη, hsupport, hsrc, hvalue⟩ :=
    exists_supportedGaugeTest_at R hs W
  obtain ⟨Z, _, hZ⟩ := exists_supportedGauge_variation R b lift η hM12 hU hlift hright hη
    hsupport hsrc
  obtain ⟨DZ⟩ := exists_variationDerivativeData Z
  have hz := jacobiResidual_supportedGauge_eq_zero hCoordinates hM04 hM12 V D hmin hfix
    hzero b lift η hU hlift hright hη hsupport hsrc Z hZ DZ.variation_extension
      s (Ioo_subset_Icc_self hs)
  have hfield : M14VariationField Z s = W := Subtype.ext
    ((variationField_supportedGauge_val R b lift η Z hZ
      (fun t ht => hright _ (hsrc t ht)) (Ioo_subset_Icc_self hs)).trans hvalue)
  rwa [hfield] at hz

end PoincareConjecture.M14
