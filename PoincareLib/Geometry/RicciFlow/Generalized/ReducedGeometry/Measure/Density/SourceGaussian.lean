import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedVolume
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Transport.BasisCoordinateVolume
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.SourceGaussian

/-!
# The horizontal source Gaussian

The Gaussian in Morgan-Tian Proposition 6.78, pp. 143-144, is measured in
the specified horizontal metric. Orthonormal basis coordinates identify
its actual coordinate measure with the Euclidean one, so M10's Gaussian
integrability and unnormalized mass apply without a normalization change.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

/-- Orthonormal coordinates identify the specified horizontal metric square
with the Euclidean norm square, as in Proposition 6.78, pp. 143-144. -/
theorem horizontal_inner_euclideanCoordinates
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) (v : EuclideanSpace ℝ (Fin n)) :
    G.spacetime.horizontalMetric.inner x
      (b.euclideanCoordinates v) (b.euclideanCoordinates v) = ‖v‖ ^ 2 := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have ho : Orthonormal ℝ b := orthonormal_iff_ite.mpr hb
  let e := (b.toOrthonormalBasis ho).repr.symm
  have hi := e.inner_map_map v v
  exact hi.trans (real_inner_self_eq_norm_sq v)

private theorem horizontalGaussian_comp_coordinates
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) :
    (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) ∘ b.euclideanCoordinates =
      fun v => (2 : ℝ) ^ n * Real.exp (-‖v‖ ^ 2) := by
  funext v
  have hpow : Real.rpow (2 : ℝ) (n : ℝ) = (2 : ℝ) ^ n := Real.rpow_natCast _ _
  simp only [Function.comp_apply, horizontal_inner_euclideanCoordinates b hb, hpow]

/-- The metric Gaussian of Proposition 6.78, pp. 143-144, is integrable for
the frozen source coordinate measure in every dimension. -/
theorem horizontalGaussian_integrable
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) :
    Integrable (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z))
      (M14HorizontalCoordinateVolume G b) := by
  have h := b.integrableOn_coordinateVolume_iff
    (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) Set.univ
  rw [horizontalGaussian_comp_coordinates b hb] at h
  simpa only [Set.preimage_univ, integrableOn_univ, M14HorizontalCoordinateVolume] using
    h.mpr (by simpa only [Set.preimage_univ, integrableOn_univ] using
      M10.sourceGaussian_integrable n)

/-- The horizontal source Gaussian has the exact unnormalized Euclidean
reduced-volume mass, Proposition 6.78 and Definition 6.70, pp. 140, 143-144. -/
theorem integral_horizontalGaussian
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) :
    (∫ Z, Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)
      ∂M14HorizontalCoordinateVolume G b) = euclideanReducedVolume n := by
  have h := b.setIntegral_coordinateVolume
    (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) Set.univ
  rw [horizontalGaussian_comp_coordinates b hb] at h
  simpa only [Set.preimage_univ, setIntegral_univ,
    M10.integral_sourceGaussian, M14HorizontalCoordinateVolume] using h

/-- The selected Jacobian data use a source measure for which the initial
Gaussian in Proposition 6.78, pp. 143-144, is integrable. -/
theorem measureData_sourceGaussian_integrable
    {T τ : ℝ} {E : M14ExponentialFamily G T x} {H : M14StableSet G T τ x E}
    (D : M14MeasureJacobianData G T τ x E H) :
    Integrable (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) D.sourceMeasure := by
  rw [D.source_volume_eq_metric_volume]
  exact horizontalGaussian_integrable D.sourceBasis D.source_basis_orthonormal

/-- The selected Jacobian data preserve the exact initial Gaussian mass in
Proposition 6.78, pp. 143-144, including dimension zero. -/
theorem measureData_integral_sourceGaussian
    {T τ : ℝ} {E : M14ExponentialFamily G T x} {H : M14StableSet G T τ x E}
    (D : M14MeasureJacobianData G T τ x E H) :
    (∫ Z, Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z) ∂D.sourceMeasure) =
      euclideanReducedVolume n := by
  rw [D.source_volume_eq_metric_volume]
  exact integral_horizontalGaussian D.sourceBasis D.source_basis_orthonormal

end PoincareMT.M14
