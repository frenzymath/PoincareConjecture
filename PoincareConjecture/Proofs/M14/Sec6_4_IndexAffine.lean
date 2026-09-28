import PoincareConjecture.Proofs.M14.Sec6_4_PullbackLinearity
import PoincareConjecture.Proofs.M14.Sec6_4_IndexAlgebra
import PoincareConjecture.Proofs.M14.Sec6_4_IndexJacobi
import PoincareConjecture.Proofs.M14.Sec6_4_SecondVariation

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem variation_index_density_affine
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V W : M14LVariationData G p R)
    (DV : M14VariationDerivativeData V) (DW : M14VariationDerivativeData W)
    (Z : ∀ s, G.Horizontal (R.curve s))
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z) (c : ℝ)
    (hfield : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      M14VariationField W s = M14VariationField V s + c • Z s)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    M14SecondVariationIndexDensity W DW s = M14SecondVariationIndexDensity V DV s +
      2 * c * pullbackIndexPairDensity R DV.variation_extension EZ s +
      c ^ 2 * pullbackIndexPairDensity R EZ EZ s := by
  have hderiv := horizontalCovariantDerivative_affine_congr DV.variation_extension EZ
    DW.variation_extension c hfield hs
      (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs)
      ((R.smooth.mono R.interval_subset s hs).mdifferentiableWithinAt (by simp))
  rw [secondVariationIndexDensity_eq_pair R W DW s, secondVariationIndexDensity_eq_pair R V DV s]
  simp only [pullbackIndexPairDensity]
  rw [hfield s hs, hderiv]
  exact horizontalIndexPairDensity_quadratic R hM04 hM12 hs (M14VariationField V s) (Z s) _ _ c

theorem variation_index_form_affine
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V W : M14LVariationData G p R)
    (DV : M14VariationDerivativeData V) (DW : M14VariationDerivativeData W)
    (Z : ∀ s, G.Horizontal (R.curve s))
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z) (c : ℝ)
    (hfield : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      M14VariationField W s = M14VariationField V s + c • Z s) :
    M14SecondVariationIndexForm W DW = M14SecondVariationIndexForm V DV +
      2 * c * (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        pullbackIndexPairDensity R DV.variation_extension EZ s) +
      c ^ 2 * (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pullbackIndexPairDensity R EZ EZ s) := by
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hI {A B : ∀ s, G.Horizontal (R.curve s)}
      (EA : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) A)
      (EB : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) B) :
      IntervalIntegrable (pullbackIndexPairDensity R EA EB) volume
        (Real.sqrt τ₁) (Real.sqrt τ₂) :=
    (pullbackIndexPairDensity_contDiffOn R (jacobiFieldDataOfExtension hCoordinates EA)
      EB hM04 hM12).continuousOn.intervalIntegrable_of_Icc hab.le
  have hVV := hI DV.variation_extension DV.variation_extension
  have hVZ := hI DV.variation_extension EZ
  have hZZ := hI EZ EZ
  have hidx : IntervalIntegrable (M14SecondVariationIndexDensity V DV) volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply hVV.congr_uIoo
    intro s hs
    exact (secondVariationIndexDensity_eq_pair R V DV s).symm
  unfold M14SecondVariationIndexForm
  calc
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, M14SecondVariationIndexDensity W DW s) =
        ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
          M14SecondVariationIndexDensity V DV s +
            2 * c * pullbackIndexPairDensity R DV.variation_extension EZ s +
            c ^ 2 * pullbackIndexPairDensity R EZ EZ s :=
      intervalIntegral.integral_congr_Ioo_of_le hab.le (fun s hs =>
        variation_index_density_affine hM04 hM12 V W DV DW Z EZ c hfield (Ioo_subset_Icc_self hs))
    _ = _ := by
      rw [intervalIntegral.integral_add (hidx.add (hVZ.const_mul _)) (hZZ.const_mul _),
        intervalIntegral.integral_add hidx (hVZ.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem index_pair_zero_of_affine_variations
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hzero : M14SecondVariationIndexForm V D = 0)
    (Z : ∀ s, G.Horizontal (R.curve s))
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z)
    (hrealize : ∀ c : ℝ, ∃ W : M14LVariationData G p R, M14BothEndpointsFixed W ∧
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
        M14VariationField W s = M14VariationField V s + c • Z s) :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      pullbackIndexPairDensity R D.variation_extension EZ s) = 0 := by
  apply M08.mixedTerm_eq_zero_of_quadratic_nonneg
    (C := ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pullbackIndexPairDensity R EZ EZ s)
  intro c
  obtain ⟨W, hfix, hfield⟩ := hrealize c
  obtain ⟨DW⟩ := exists_variationDerivativeData W
  have hnonneg := secondVariationIndexForm_nonneg hCoordinates hM04 hM12 W DW hmin hfix
  rw [variation_index_form_affine hM04 hM12 V W D DW Z EZ c hfield, hzero, zero_add] at hnonneg
  exact hnonneg

end PoincareConjecture.M14
