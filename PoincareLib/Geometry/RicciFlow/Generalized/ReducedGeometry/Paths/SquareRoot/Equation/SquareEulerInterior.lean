import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Extension.LocalTestField
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Euler.EulerResidual
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.IndexPositivity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.IntervalTestFunctions

/-!
# Interior Euler equation for a smooth minimizing square path

Morgan-Tian Lemma 6.4 and Definition 6.7, pp. 107-108. Actual supported
gauge variations and scalar test functions force the frozen paired Euler
residual to vanish against every horizontal vector in the interior.
The argument assumes the supplied smooth square-root representative;
regularity of a general minimizing path is a separate step.
-/

set_option autoImplicit false
-- The compared variation fields have the same actual horizontal base fiber.
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

/-- A minimizing path annihilates the continuous residual representative
of each supported gauge test field, the fundamental-lemma step after
Lemma 6.4, pp. 107-108. -/
theorem variationEulerDensity_supportedGauge_eq_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U) (V : M14LVariationData G p R)
    (hV : ∀ s v, V.squareFamily s v = supportedGaugeFamily R b lift η (s, v)) :
    ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, variationEulerDensity V s = 0 := by
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hcont := (variationEulerDensity_contDiffOn hM12 V).continuousOn
  apply hcont.eq_zero_of_intervalIntegral_contDiff_smul hab
  intro ψ hψ _ _
  let ξ := fun s => ψ s • η s
  have hξ : ContDiff ℝ ∞ ξ := hψ.smul hη
  have hξη : tsupport ξ ⊆ tsupport η := tsupport_smul_subset_right ψ η
  obtain ⟨Vξ, hfixξ, hVξ⟩ := exists_supportedGauge_variation R b lift ξ hM12 hU hlift
    hright hξ (hξη.trans hsupport) (fun s hs => hsrc s (hξη hs))
  obtain ⟨Dξ⟩ := exists_variationDerivativeData Vξ
  have hfield (s : ℝ) (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
      M14VariationField Vξ s = ψ s • M14VariationField V s := by
    apply Subtype.ext
    have hξval := variationField_supportedGauge_val R b lift ξ Vξ hVξ
      (fun t ht => hright _ (hsrc t (hξη ht))) hs
    have hηval := variationField_supportedGauge_val R b lift η V hV
      (fun t ht => hright _ (hsrc t ht)) hs
    have hlinear := congrArg Subtype.val (((G.gaugeCover.metric b).spatialTangentEquiv
      (lift (R.curve s)).1 (lift (R.curve s)).2).map_smul (ψ s) (η s))
    exact hξval.trans (hlinear.trans
      (congrArg (fun w : SpacetimeModelVector n => ψ s • w) hηval.symm))
  have hz := firstVariationResidualIntegral_eq_zero hCoordinates hM12 Vξ Dξ hmin hfixξ
  change (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
    -M14SquareRootEulerResidual G R Dξ.base_extension s (M14VariationField Vξ s)) = 0 at hz
  rw [intervalIntegral.integral_neg, neg_eq_zero] at hz
  rw [← hz]
  apply intervalIntegral.integral_congr_Ioo_of_le hab.le
  intro s hs
  change ψ s • variationEulerDensity V s =
    M14SquareRootEulerResidual G R Dξ.base_extension s (M14VariationField Vξ s)
  rw [variationEulerDensity_eq_residual hCoordinates hM12 V Dξ.base_extension hs,
    hfield s (Ioo_subset_Icc_self hs), squareRootEulerResidual_smul hM12, smul_eq_mul]

/-- A supplied smooth square-root representative of a minimizing path
satisfies the actual paired Euler equation at every interior time,
Definition 6.7, p. 108. -/
theorem squareRootEulerResidual_eq_zero_of_minimizing_interior
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (W : G.Horizontal (R.curve s)) :
    M14SquareRootEulerResidual G R E s W = 0 := by
  obtain ⟨b, U, lift, hU, hlift, hright, η, hη, hsupport, hsrc, hvalue⟩ :=
    exists_supportedGaugeTest_at R hs W
  obtain ⟨V, _, hV⟩ := exists_supportedGauge_variation R b lift η hM12 hU hlift hright hη
    hsupport hsrc
  have hz := variationEulerDensity_supportedGauge_eq_zero hCoordinates hM12 hmin b lift η
    hU hlift hright hη hsupport hsrc V hV s (Ioo_subset_Icc_self hs)
  rw [variationEulerDensity_eq_residual hCoordinates hM12 V E hs] at hz
  have hfield : M14VariationField V s = W := Subtype.ext
    ((variationField_supportedGauge_val R b lift η V hV
      (fun t ht => hright _ (hsrc t ht)) (Ioo_subset_Icc_self hs)).trans hvalue)
  rwa [hfield] at hz

end PoincareMT.M14
