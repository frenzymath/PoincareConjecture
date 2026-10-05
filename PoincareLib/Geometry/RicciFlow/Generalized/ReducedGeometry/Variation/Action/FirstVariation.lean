import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Action.VariationDensity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Action.VariationBoundary
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Theory

/-!
# First variation of the generalized L-action

Morgan-Tian Lemma 6.4, pp. 107-108, with the square-root substitution
of equation (6.2), p. 106. The actual density partial is the derivative
of the boundary pair minus the frozen Euler residual. The interval
argument follows M08 FirstVariation and applies at a zero initial time.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

/-- The first density variation equals the boundary-pair derivative
minus the actual paired Euler residual, Lemma 6.4, pp. 107-108. -/
theorem firstVariation_density_identity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
        (variationActionDensity V) (s, 0) =
      derivWithin (variationBoundaryPair V) (M14SqrtParameterInterval τ₁ τ₂) s -
        M14SquareRootEulerResidual G R D.base_extension s (M14VariationField V s) := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hsC : s ∈ M14SqrtParameterInterval τ₁ τ₂ := Ioo_subset_Icc_self hs
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hraw := M08.hasDerivAt_variationParameter hP (variationActionDensity V)
    (variationActionDensity_contDiffOn hM12 V) hsC hzero
  have hvalue := hraw.unique (hasDerivAt_variationActionDensity_zero hCoordinates hM12 V D hs)
  have hB := (hasDerivWithinAt_variationBoundaryPair V D hsC).derivWithin
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hsC)
  rw [hvalue, hB]
  unfold M14SquareRootEulerResidual M14SquareRootVelocity
  ring

/-- The frozen first-variation identity holds for every supplied actual
derivative record, including paths starting at zero, Lemma 6.4, pp. 107-108. -/
theorem firstVariationIdentity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V) :
    M14FirstVariationIdentity V D := by
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  let C := M14SqrtParameterInterval τ₁ τ₂
  let raw := fun s => M08.variationParameterDeriv C V.parameterDomain
    (variationActionDensity V) (s, 0)
  let B := variationBoundaryPair V
  let dB := derivWithin B C
  let Res := fun s => M14SquareRootEulerResidual G R D.base_extension s (M14VariationField V s)
  have hab : a < b := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hab
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hraw : ContinuousOn raw C :=
    (M08.variationParameterDeriv_contDiffOn hC hP (variationActionDensity V)
      (variationActionDensity_contDiffOn hM12 V)).continuousOn.comp
        (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hzero⟩)
  have hB : ContDiffOn ℝ ∞ B C := variationBoundaryPair_contDiffOn V
  have hdB : ContinuousOn dB C := (hB.derivWithin hC (m := ∞) (by simp)).continuousOn
  have hrawInt : IntervalIntegrable raw volume a b := hraw.intervalIntegrable_of_Icc hab.le
  have hdBInt : IntervalIntegrable dB volume a b := hdB.intervalIntegrable_of_Icc hab.le
  have hid (s : ℝ) (hs : s ∈ Ioo a b) : raw s = dB s - Res s :=
    firstVariation_density_identity hCoordinates hM12 V D hs
  have hResInt : IntervalIntegrable Res volume a b := by
    apply (hdBInt.sub hrawInt).congr_uIoo
    intro s hs
    rw [uIoo_of_le hab.le] at hs
    have h := hid s hs
    linarith
  have hFTC : (∫ s in a..b, dB s) = B b - B a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hB.continuousOn
      (fun s hs => (((hB s (Ioo_subset_Icc_self hs)).differentiableWithinAt
        (by simp)).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds hs.1 hs.2)) hdBInt
  have hvalue : (∫ s in a..b, raw s) =
      M14FirstVariationBoundaryTerm V + M14FirstVariationResidualIntegral V D := by
    calc
      (∫ s in a..b, raw s) = ∫ s in a..b, dB s + -Res s :=
        intervalIntegral.integral_congr_Ioo_of_le hab.le (fun s hs => by
          simpa only [sub_eq_add_neg] using hid s hs)
      _ = (∫ s in a..b, dB s) + ∫ s in a..b, -Res s :=
        intervalIntegral.integral_add hdBInt hResInt.neg
      _ = _ := by rw [hFTC]; rfl
  have h := hasDerivAt_variationAction_integral hM12 V hzero
  change HasDerivAt (M14VariationAction V) (∫ s in a..b, raw s) 0 at h
  rwa [hvalue] at h

/-- The exact frozen generalized first-variation statement,
with its actual extension witnesses, Lemma 6.4, pp. 107-108. -/
theorem firstVariationStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) : M14FirstVariationStatement G := by
  intro T τ₁ τ₂ x y p R V
  obtain ⟨D⟩ := exists_variationDerivativeData V
  exact ⟨D, firstVariationIdentity hCoordinates hM12 V D⟩

end PoincareMT.M14
