import PoincareConjecture.Proofs.M08.SupportedIndexVariation
import PoincareConjecture.Proofs.M08.JacobiTestFields
import PoincareConjecture.Proofs.M08.WeakMomentum
import Mathlib.MeasureTheory.Measure.OpenPos

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

theorem supported_jacobi_residual_integral_eq_zero
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p) (R : RegularizedLGeodesicData p)
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
      pullbackJacobiPairDensity F T D.variation_extension
        (variationSqrtRegularField V.toLVariation D).derivative_extension
        (fun r ↦ chartFrame x (η r) (V.toLVariation.baseSquareCurve r)) s) = 0 := by
  let A := variationSqrtRegularPath V.toLVariation
  let Q := variationSqrtRegularField V.toLVariation D
  have hab := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have hI := index_pair_zero_of_index_zero hM04 hmin R V D hzero x η hη hsrc hleft hright Eη
  have hG := integral_pullbackIndexPairDensity F hM04 T hab
    (fun s hs ↦ p.time_mem _ (square_mem_backward_interval p hs))
    A.open_domain A.interval_subset A.curve A.smooth (squareVariationField V.toLVariation)
    (fun r ↦ chartFrame x (η r) (V.toLVariation.baseSquareCurve r))
    D.variation_extension Q.derivative_extension Eη
  rw [hI] at hG
  simp only [pullbackIndexBoundaryPair, hleft, hright, chartFrame, map_zero,
    sub_self, zero_sub] at hG
  exact neg_eq_zero.mp hG.symm

set_option maxHeartbeats 1600000 in
theorem supported_jacobi_residual_eq_zero
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p) (R : RegularizedLGeodesicData p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V.toLVariation)
    (hzero : secondVariationIndexForm V.toLVariation D = 0)
    (x : M) (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.toLVariation.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Eη : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂)
      V.toLVariation.baseSquareCurve
      (fun s ↦ chartFrame x (η s) (V.toLVariation.baseSquareCurve s))) :
    ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      pullbackJacobiPairDensity F T D.variation_extension
        (variationSqrtRegularField V.toLVariation D).derivative_extension
        (fun r ↦ chartFrame x (η r) (V.toLVariation.baseSquareCurve r)) s = 0 := by
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  let A := variationSqrtRegularPath V.toLVariation
  let Q := variationSqrtRegularField V.toLVariation D
  let f := pullbackJacobiPairDensity F T D.variation_extension Q.derivative_extension
    (fun r ↦ chartFrame x (η r) (V.toLVariation.baseSquareCurve r))
  have hab : a < b := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have htime (s : ℝ) (hs : s ∈ Icc a b) : T - s ^ 2 ∈ J :=
    p.time_mem _ (square_mem_backward_interval p hs)
  have hf : ContinuousOn f (Icc a b) :=
    (pullbackJacobiPairDensity_contDiffOn F hM04 T hab htime
      A.open_domain A.interval_subset A.curve A.smooth _ _
      D.variation_extension Q.derivative_extension Eη).continuousOn
  have htest (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ Ioo a b) : (∫ s in a..b, ψ s • f s) = 0 := by
    let ξ := fun r ↦ ψ r • η r
    have hξ : ContDiff ℝ ∞ ξ := hψ.smul hη
    have hξsrc (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
        (hmem : s ∈ tsupport ξ) :
        V.toLVariation.baseSquareCurve s ∈
          (chartAt (EuclideanSpace ℝ (Fin n)) x).source :=
      hsrc s hs (tsupport_smul_subset_right ψ η hmem)
    have hξleft : ξ a = 0 := by
      have hnot : a ∉ tsupport ψ := fun h ↦ (lt_irrefl a) (hψs h).1
      simp only [ξ, image_eq_zero_of_notMem_tsupport hnot, zero_smul]
    have hξright : ξ b = 0 := by
      have hnot : b ∉ tsupport ψ := fun h ↦ (lt_irrefl b) (hψs h).2
      simp only [ξ, image_eq_zero_of_notMem_tsupport hnot, zero_smul]
    obtain ⟨Eξ⟩ := exists_supportedChartFieldExtension hM04 V D x ξ hξ hξsrc hξleft hξright
    have hξzero := supported_jacobi_residual_integral_eq_zero hM04 hmin R V D hzero
      x ξ hξ hξsrc hξleft hξright Eξ
    rw [← hξzero]
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    have hsC : s ∈ Icc a b := Ioo_subset_Icc_self hs
    change ψ s • jacobiPairResidual F T A.curve (Icc a b) s
        (squareVariationField V.toLVariation s) (Q.firstDerivative s)
        (Q.secondDerivative s) (chartFrame x (η s) (A.curve s)) =
      jacobiPairResidual F T A.curve (Icc a b) s
        (squareVariationField V.toLVariation s) (Q.firstDerivative s)
        (Q.secondDerivative s) (chartFrame x (ψ s • η s) (A.curve s))
    rw [show chartFrame x (ψ s • η s) (A.curve s) =
        ψ s • chartFrame x (η s) (A.curve s) by simp only [chartFrame, map_smul],
      jacobiPairResidual_smul_right F hM04 T hab htime A.curve hsC
        (variationBaseSquare_mdifferentiableAt V.toLVariation hsC), smul_eq_mul]
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    ((hf.mono Ioo_subset_Icc_self).locallyIntegrableOn (μ := volume) measurableSet_Ioo)
    (fun ψ hψ hψc hψs ↦ by
      rw [← intervalIntegral.integral_eq_integral_of_support_subset
        (f := fun s ↦ ψ s • f s)
        ((Function.support_smul_subset_left ψ f).trans
          ((subset_tsupport ψ).trans (hψs.trans Ioo_subset_Ioc_self)))]
      exact htest ψ hψ hψc hψs)
  have hrestricted : f =ᵐ[volume.restrict (Icc a b)] 0 := by
    change ∀ᵐ s ∂volume.restrict (Icc a b), f s = 0
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hrestricted hf continuousOn_const

theorem isLJacobiField_of_index_zero (hM04 : RicciFlowCurvatureTheory.{u})
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p) (R : RegularizedLGeodesicData p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V.toLVariation)
    (hzero : secondVariationIndexForm V.toLVariation D = 0) :
    IsLJacobiField F T τ₁ τ₂ p (variationField V.toLVariation) := by
  let A := variationSqrtRegularPath V.toLVariation
  let Q := variationSqrtRegularField V.toLVariation D
  let RV := variationRegularizedGeodesicData V.toLVariation D R
  have hab := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  refine ⟨RV, Q, ?_, ?_⟩
  · have hleft := squareVariationField_eq_zero_of_constant V.toLVariation
      (Real.sqrt τ₁) (p.curve τ₁)
      (fun _ hu ↦ squareFamily_left_eq V.toInitialFixedLVariation hu)
    have hbridge := squareVariationField_agrees_backward V.toLVariation
      (show Real.sqrt τ₁ ∈ sqrtParameterInterval τ₁ τ₂ from ⟨le_rfl, hab.le⟩)
    rw [Real.sq_sqrt p.nonnegative] at hbridge
    exact hbridge.symm.trans hleft
  · intro s hs W
    obtain ⟨x, η, hη, hsrc, hvalue⟩ := exists_supportedChartTest_at
      A.open_domain A.interval_subset A.curve A.smooth hs W
    have hfield := supportedChartField_contMDiffOn A.open_domain A.interval_subset
      A.curve A.smooth x η hη hsrc
    obtain ⟨Eη⟩ := exists_closedSectionExtension hab A.open_domain A.interval_subset
      A.curve A.smooth (fun r ↦ chartFrame x (η r) (A.curve r)) hfield
    have hz := supported_jacobi_residual_eq_zero hM04 hmin R V D hzero x η hη hsrc Eη s hs
    change jacobiPairResidual F T A.curve (sqrtParameterInterval τ₁ τ₂) s
      (Q.field s) (Q.firstDerivative s) (Q.secondDerivative s)
      (chartFrame x (η s) (A.curve s)) = 0 at hz
    rw [hvalue] at hz
    exact hz

theorem index_zero_of_isLJacobiField (hM04 : RicciFlowCurvatureTheory.{u})
    (R : RegularizedLGeodesicData p) (V : FixedEndpointLVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V.toLVariation)
    (hJacobi : IsLJacobiField F T τ₁ τ₂ p (variationField V.toLVariation)) :
    secondVariationIndexForm V.toLVariation D = 0 := by
  let A := variationSqrtRegularPath V.toLVariation
  let Q := variationSqrtRegularField V.toLVariation D
  let RV := variationRegularizedGeodesicData V.toLVariation D R
  have hab := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  obtain ⟨R₀, Q₀, _, hres⟩ := hJacobi
  have hresV (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
      pullbackJacobiPairDensity F T D.variation_extension Q.derivative_extension
        (squareVariationField V.toLVariation) s = 0 := by
    have heq := regularizedJacobiResidual_representative_eq R₀ RV Q₀ Q hs
      (squareVariationField V.toLVariation s)
    exact heq.symm.trans (hres s hs _)
  have hleft := squareVariationField_eq_zero_of_constant V.toLVariation
    (Real.sqrt τ₁) (p.curve τ₁)
    (fun _ hu ↦ squareFamily_left_eq V.toInitialFixedLVariation hu)
  have hright := squareVariationField_eq_zero_of_constant V.toLVariation
    (Real.sqrt τ₂) (p.curve τ₂) (fun _ hu ↦ squareFamily_right_eq V hu)
  have hG := integral_pullbackIndexPairDensity F hM04 T hab
    (fun s hs ↦ p.time_mem _ (square_mem_backward_interval p hs))
    A.open_domain A.interval_subset A.curve A.smooth _ _
    D.variation_extension Q.derivative_extension D.variation_extension
  have hpair : secondVariationIndexForm V.toLVariation D =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        pullbackIndexPairDensity F T D.variation_extension D.variation_extension s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    exact secondVariationIndexDensity_eq_pair hM04 V.toLVariation D (Ioo_subset_Icc_self hs)
  have hresint : (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      pullbackJacobiPairDensity F T D.variation_extension Q.derivative_extension
        (squareVariationField V.toLVariation) s) = 0 := by
    rw [← intervalIntegral.integral_zero (μ := volume) (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)]
    exact intervalIntegral.integral_congr_Ioo_of_le hab.le
      (fun s hs ↦ hresV s (Ioo_subset_Icc_self hs))
  rw [hpair, hG, hresint]
  simp only [pullbackIndexBoundaryPair, hleft, hright, map_zero, sub_self]

theorem exists_fixedEndpointSecondVariation (hM04 : RicciFlowCurvatureTheory.{u})
    (hmin : IsMinimizingBackwardLPath F T τ₁ τ₂ p) (R : RegularizedLGeodesicData p)
    (V : FixedEndpointLVariation F T τ₁ τ₂ p) :
    ∃ D : LVariationDerivativeData V.toLVariation, ∃ q : ℝ,
      HasDerivAt (fun u ↦ deriv (variationLLength V.toLVariation) u) q 0 ∧
        q = secondVariationIndexForm V.toLVariation D ∧
        (q = 0 ↔ IsLJacobiField F T τ₁ τ₂ p (variationField V.toLVariation)) := by
  obtain ⟨D⟩ := exists_variationDerivativeData V.toLVariation
  refine ⟨D, secondVariationIndexForm V.toLVariation D, ?_, rfl, ?_⟩
  · simpa only [secondVariationBoundaryTerm_eq_zero V D, zero_add] using
      hasDerivAt_secondVariation hM04 V.toLVariation D R
  · exact ⟨isLJacobiField_of_index_zero hM04 hmin R V D,
      index_zero_of_isLJacobiField hM04 R V D⟩

end PoincareConjecture.M08
