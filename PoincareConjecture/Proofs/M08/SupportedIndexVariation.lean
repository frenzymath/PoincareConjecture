import PoincareConjecture.Proofs.M08.SupportedChartField
import PoincareConjecture.Proofs.M08.PullbackLinearity
import PoincareConjecture.Proofs.M08.IndexGreen
import PoincareConjecture.Proofs.M08.SecondVariation
import PoincareConjecture.Proofs.M08.IndexPositivity
import PoincareConjecture.Proofs.M08.JacobiTestFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
  {p : BackwardTimePath F T τ₁ τ₂}

theorem exists_supportedChartFieldExtension (hM04 : RicciFlowCurvatureTheory.{u})
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V.toLVariation)
    (x : M) (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.toLVariation.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hleft : η (Real.sqrt τ₁) = 0) (hright : η (Real.sqrt τ₂) = 0) :
    Nonempty (ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂)
      V.toLVariation.baseSquareCurve
        (fun s ↦ chartFrame x (η s) (V.toLVariation.baseSquareCurve s))) := by
  let A := variationSqrtRegularPath V.toLVariation
  exact exists_closedSectionExtension (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
    A.open_domain A.interval_subset A.curve A.smooth _
    (supportedChartField_contMDiffOn A.open_domain A.interval_subset A.curve A.smooth x η hη hsrc)

set_option maxHeartbeats 1200000 in
theorem variation_index_density_affine (hM04 : RicciFlowCurvatureTheory.{u})
    (V W : LVariation F T τ₁ τ₂ p)
    (DV : LVariationDerivativeData V) (DW : LVariationDerivativeData W)
    (Z : ∀ s, TangentSpace (𝓡 n) (V.baseSquareCurve s))
    (EZ : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) V.baseSquareCurve Z)
    (c : ℝ)
    (hfield : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      squareVariationField W s = squareVariationField V s + c • Z s)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    secondVariationIndexDensity W DW s = secondVariationIndexDensity V DV s +
      2 * c * pullbackIndexPairDensity F T DV.variation_extension EZ s +
      c ^ 2 * pullbackIndexPairDensity F T EZ EZ s := by
  let C := sqrtParameterInterval τ₁ τ₂
  have hcurve : EqOn W.baseSquareCurve V.baseSquareCurve C :=
    sqrtRegularPath_eqOn (variationSqrtRegularPath W) (variationSqrtRegularPath V)
  have hab : Real.sqrt τ₁ < Real.sqrt τ₂ := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have hderiv : pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) W.baseSquareCurve
      (squareVariationField W) C DW.variation_extension s =
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
      (squareVariationField V) C DV.variation_extension s +
      c • pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve Z C EZ s := by
    rw [pullbackCovariantDerivative_congr F (fun r ↦ T - r ^ 2) hcurve hfield
      DW.variation_extension (affineParametricExtension DV.variation_extension EZ c) hs
      (uniqueDiffOn_Icc hab s hs) (variationBaseSquare_mdifferentiableAt V hs)]
    exact pullbackCovariantDerivative_affine F _ DV.variation_extension EZ c hs
  have hvelocity := curveVelocityWithin_congr (n := n) hcurve hs
  have hpair : regularizedIndexPairDensity F T W.baseSquareCurve C s
        (squareVariationField W s) (squareVariationField W s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) W.baseSquareCurve
          (squareVariationField W) C DW.variation_extension s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) W.baseSquareCurve
          (squareVariationField W) C DW.variation_extension s) =
      regularizedIndexPairDensity F T V.baseSquareCurve C s
        (squareVariationField V s + c • Z s) (squareVariationField V s + c • Z s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
          (squareVariationField V) C DV.variation_extension s +
          c • pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve Z C EZ s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
          (squareVariationField V) C DV.variation_extension s +
          c • pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve Z C EZ s) := by
    unfold regularizedIndexPairDensity jacobiPairResidual
    rw [hderiv, hfield s hs, hvelocity, hcurve hs]
  rw [secondVariationIndexDensity_eq_pair hM04 W DW hs, hpair,
    secondVariationIndexDensity_eq_pair hM04 V DV hs]
  exact regularizedIndexPairDensity_quadratic F hM04 T hab
    (fun r hr ↦ p.time_mem _ (square_mem_backward_interval p hr)) V.baseSquareCurve hs
    (variationBaseSquare_mdifferentiableAt V hs) (squareVariationField V s) (Z s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
      (squareVariationField V) C DV.variation_extension s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve Z C EZ s) c

theorem variation_index_form_affine (hM04 : RicciFlowCurvatureTheory.{u})
    (V W : LVariation F T τ₁ τ₂ p)
    (DV : LVariationDerivativeData V) (DW : LVariationDerivativeData W)
    (Z : ∀ s, TangentSpace (𝓡 n) (V.baseSquareCurve s))
    (EZ : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) V.baseSquareCurve Z)
    (c : ℝ)
    (hfield : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      squareVariationField W s = squareVariationField V s + c • Z s) :
    secondVariationIndexForm W DW = secondVariationIndexForm V DV +
      2 * c * (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        pullbackIndexPairDensity F T DV.variation_extension EZ s) +
      c ^ 2 * (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pullbackIndexPairDensity F T EZ EZ s) := by
  let R := variationSqrtRegularPath V
  have hab : Real.sqrt τ₁ < Real.sqrt τ₂ := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have htime (r : ℝ) (hr : r ∈ sqrtParameterInterval τ₁ τ₂) : T - r ^ 2 ∈ J :=
    p.time_mem _ (square_mem_backward_interval p hr)
  have hI (A B : ∀ s, TangentSpace (𝓡 n) (V.baseSquareCurve s))
      (EA : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) V.baseSquareCurve A)
      (EB : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) V.baseSquareCurve B) :
      IntervalIntegrable (pullbackIndexPairDensity F T EA EB) volume
        (Real.sqrt τ₁) (Real.sqrt τ₂) :=
    (pullbackIndexPairDensity_contDiffOn F hM04 T hab htime R.open_domain R.interval_subset
      R.curve R.smooth A B EA EB).continuousOn.intervalIntegrable_of_Icc hab.le
  have hVV := hI _ _ DV.variation_extension DV.variation_extension
  have hVZ := hI _ _ DV.variation_extension EZ
  have hZZ := hI _ _ EZ EZ
  have hidx : IntervalIntegrable (secondVariationIndexDensity V DV) volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply hVV.congr_uIoo
    intro s hs
    rw [uIoo_of_le hab.le] at hs
    exact (secondVariationIndexDensity_eq_pair hM04 V DV (Ioo_subset_Icc_self hs)).symm
  unfold secondVariationIndexForm
  calc
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, secondVariationIndexDensity W DW s) =
        ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
          secondVariationIndexDensity V DV s +
            2 * c * pullbackIndexPairDensity F T DV.variation_extension EZ s +
            c ^ 2 * pullbackIndexPairDensity F T EZ EZ s :=
      intervalIntegral.integral_congr_Ioo_of_le hab.le (fun s hs ↦
        variation_index_density_affine hM04 V W DV DW Z EZ c hfield (Ioo_subset_Icc_self hs))
    _ = _ := by
      rw [intervalIntegral.integral_add (hidx.add (hVZ.const_mul _)) (hZZ.const_mul _),
        intervalIntegral.integral_add hidx (hVZ.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem index_pair_zero_of_index_zero (hM04 : RicciFlowCurvatureTheory.{u})
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p)
    (R : RegularizedLGeodesicData p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V.toLVariation)
    (hzero : secondVariationIndexForm V.toLVariation D = 0)
    (x : M) (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.toLVariation.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hleft : η (Real.sqrt τ₁) = 0) (hright : η (Real.sqrt τ₂) = 0)
    (Eη : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂)
      V.toLVariation.baseSquareCurve
      (fun s ↦ chartFrame x (η s) (V.toLVariation.baseSquareCurve s))) :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      pullbackIndexPairDensity F T D.variation_extension Eη s) = 0 := by
  apply mixedTerm_eq_zero_of_quadratic_nonneg
    (C := ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pullbackIndexPairDensity F T Eη Eη s)
  intro c
  obtain ⟨W, _, hfamily, _⟩ := exists_supportedChartVariation hM04 V x η hη c hsrc hleft hright
  obtain ⟨DW⟩ := exists_variationDerivativeData W.toLVariation
  have hnonneg := secondVariation_nonneg hM04 hmin W
    (hasDerivAt_secondVariation hM04 W.toLVariation DW R)
  rw [secondVariationBoundaryTerm_eq_zero W DW, zero_add] at hnonneg
  rw [variation_index_form_affine hM04 V.toLVariation W.toLVariation D DW _ Eη c
    (fun s hs ↦ supportedChartVariation_squareField V.toLVariation W.toLVariation x η hη c
      hfamily hsrc hs), hzero, zero_add] at hnonneg
  exact hnonneg

end PoincareConjecture.M08
