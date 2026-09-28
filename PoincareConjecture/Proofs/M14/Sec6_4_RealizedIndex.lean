import PoincareConjecture.Proofs.M14.Sec6_4_FieldRealization
import PoincareConjecture.Proofs.M14.Sec6_4_IndexAffine

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

theorem secondVariationIndexDensity_eq_of_field
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (hfield : ∀ s ∈ M14SqrtParameterInterval a b, M14VariationField V s = Y s)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b) :
    M14SecondVariationIndexDensity V D s = pullbackIndexPairDensity R EY EY s := by
  let E' := pullbackExtensionCongrOn D.variation_extension (fun _ _ => rfl)
    (fun r hr => heq_of_eq (hfield r hr))
  have hd := (eq_of_heq (horizontalCovariantDerivative_congrOn D.variation_extension
    (fun _ _ => rfl) (fun r hr => heq_of_eq (hfield r hr)) hs)).trans
      (horizontalCovariantDerivative_extension_independent E' EY hs
        (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs)
        ((R.smooth.mono R.interval_subset s hs).mdifferentiableWithinAt (by simp)))
  rw [secondVariationIndexDensity_eq_pair R V D]
  simp only [pullbackIndexPairDensity, hfield s hs, hd]

theorem secondVariationIndexForm_eq_of_field
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (hfield : ∀ s ∈ M14SqrtParameterInterval a b, M14VariationField V s = Y s) :
    M14SecondVariationIndexForm V D =
      ∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EY s := by
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.tau_lt.le)
  intro s hs
  exact secondVariationIndexDensity_eq_of_field V D EY hfield (Ioo_subset_Icc_self hs)

theorem pullback_index_form_nonneg
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hmin : M14IsMinimizing p) {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (hleft : Y (Real.sqrt a) = 0) (hright : Y (Real.sqrt b) = 0) :
    0 ≤ ∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EY s := by
  have hY := pullbackExtension_field_contMDiffOn EY (R.smooth.mono R.interval_subset)
  obtain ⟨V, hfix, hfield, hterminal⟩ :=
    exists_initialFixed_variation_of_smooth_horizontalField R hM12 Y hY hleft
  obtain ⟨D⟩ := exists_variationDerivativeData V
  rw [← secondVariationIndexForm_eq_of_field V D EY hfield]
  exact secondVariationIndexForm_nonneg hCoordinates hM04 hM12 V D hmin ⟨hfix, hterminal hright⟩

end PoincareConjecture.M14
