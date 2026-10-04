import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Fields.VariationPaths
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Action.VariationAction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Action.FirstVariation
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.FixedEndpointBoundary
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.IndexPositivity

/-!
# Positivity consequences for actual fixed-endpoint variations

Morgan-Tian Lemma 6.4 and Proposition 6.33, pp. 107-108, 121-122.
Admissible variation slices give an actual local action minimum. M08's
generic scalar second-derivative theorem gives nonnegativity. The index
form consequence explicitly takes the geometric variation identity as
input; this module does not assume that identity through a new definition.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

/-- The actual second derivative of a fixed-endpoint variation at a
minimizing path is nonnegative, Proposition 6.33, pp. 121-122. -/
theorem secondDerivative_variationAction_nonneg (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (hmin : M14IsMinimizing p)
    (hfix : M14BothEndpointsFixed V) {d : ℝ}
    (hd : HasDerivAt (fun u => deriv (M14VariationAction V) u) d 0) : 0 ≤ d := by
  have hz : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  exact M08.secondDerivative_nonneg_of_localMin (isLocalMin_variationAction V hmin hfix)
    (hasDerivAt_variationAction_integral hM12 V hz).continuousAt hd

/-- At a minimizing fixed-endpoint variation, a proved first-variation
identity forces its actual residual integral to vanish, Lemma 6.4,
pp. 107-108. -/
theorem firstVariationResidualIntegral_eq_zero_of_identity (V : M14LVariationData G p R)
    (D : M14VariationDerivativeData V) (hmin : M14IsMinimizing p)
    (hfix : M14BothEndpointsFixed V) (hid : M14FirstVariationIdentity V D) :
    M14FirstVariationResidualIntegral V D = 0 := by
  have h := hasDerivAt_variationAction_eq_zero V hmin hfix hid
  simpa only [firstVariationBoundaryTerm_eq_zero V hfix, zero_add] using h

/-- The actual paired residual integral vanishes for every fixed-endpoint
variation of a minimizing path, Lemma 6.4, pp. 107-108. -/
theorem firstVariationResidualIntegral_eq_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hmin : M14IsMinimizing p) (hfix : M14BothEndpointsFixed V) :
    M14FirstVariationResidualIntegral V D = 0 :=
  firstVariationResidualIntegral_eq_zero_of_identity V D hmin hfix
    (firstVariationIdentity hCoordinates hM12 V D)

/-- A proved second-variation identity identifies the nonnegative second
derivative with the actual fixed-endpoint index form, Proposition 6.33,
pp. 121-122. -/
theorem secondVariationIndexForm_nonneg_of_identity (V : M14LVariationData G p R)
    (D : M14VariationDerivativeData V) (hmin : M14IsMinimizing p)
    (hfix : M14BothEndpointsFixed V) (hid : M14SecondVariationIdentity V D) :
    0 ≤ M14SecondVariationIndexForm V D := by
  obtain ⟨⟨d₁, hd₁, _⟩, ⟨d₂, hd₂, heq⟩⟩ := hid
  have h := M08.secondDerivative_nonneg_of_localMin
    (isLocalMin_variationAction V hmin hfix) hd₁.continuousAt hd₂
  rwa [heq, secondVariationBoundaryTerm_eq_zero V D hfix, zero_add] at h

end PoincareMT.M14
