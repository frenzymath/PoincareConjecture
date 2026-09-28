import PoincareConjecture.Definitions.M14MeasureTransport
import PoincareConjecture.Proofs.M14.Mathlib.BasisCoordinateVolume
import PoincareConjecture.Proofs.M10.SourceGaussian

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

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

theorem measureData_sourceGaussian_integrable
    {T τ : ℝ} {E : M14ExponentialFamily G T x} {H : M14StableSet G T τ x E}
    (D : M14MeasureJacobianData G T τ x E H) :
    Integrable (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) D.sourceMeasure := by
  rw [D.source_volume_eq_metric_volume]
  exact horizontalGaussian_integrable D.sourceBasis D.source_basis_orthonormal

theorem measureData_integral_sourceGaussian
    {T τ : ℝ} {E : M14ExponentialFamily G T x} {H : M14StableSet G T τ x E}
    (D : M14MeasureJacobianData G T τ x E H) :
    (∫ Z, Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z) ∂D.sourceMeasure) =
      euclideanReducedVolume n := by
  rw [D.source_volume_eq_metric_volume]
  exact integral_horizontalGaussian D.sourceBasis D.source_basis_orthonormal

end PoincareConjecture.M14
