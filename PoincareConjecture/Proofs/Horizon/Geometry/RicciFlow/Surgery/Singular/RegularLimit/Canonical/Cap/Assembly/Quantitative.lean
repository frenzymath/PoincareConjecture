import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Gradient.Persistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.ScalarEvolution








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M]


structure CapQuantitativeData (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (C : ℝ) (carrier core : Set M) where
  scalar_pos : ∀ x ∈ carrier, 0 < D.scalarCurvature x
  intrinsic_diameter_bound : intrinsicDiameter g carrier <
    ENNReal.ofReal (C * scalarCurvatureSupOn g D carrier ^ (-1 / 2 : ℝ))
  scalar_ratio : ∃ b : ℝ, b < C ∧ ∀ x ∈ carrier, ∀ y ∈ carrier,
    D.scalarCurvature y ≤ b * D.scalarCurvature x
  volume_bound : calibratedMetricVolume g carrier <
    ENNReal.ofReal C * ENNReal.ofReal (scalarCurvatureSupOn g D carrier ^ (-3 / 2 : ℝ))
  core_radius : M → ℝ
  core_radius_pos : ∀ y ∈ core, 0 < core_radius y
  core_radius_eq : ∀ y ∈ core,
    scalarCurvatureSupOn g D (g.ball y (core_radius y)) = (core_radius y)⁻¹ ^ 2
  core_ball_subset : ∀ y ∈ core, closure (g.ball y (core_radius y)) ⊆ carrier
  core_ball_compact : ∀ y ∈ core, IsCompact (closure (g.ball y (core_radius y)))
  core_ball_volume_lower : ∃ b : ℝ, C⁻¹ < b ∧ ∀ y ∈ core,
    ENNReal.ofReal (b * core_radius y ^ 3) ≤ calibratedMetricVolume g (g.ball y (core_radius y))
  gradient_bound : ∃ b : ℝ, b < C ∧ ∀ x ∈ carrier,
    scalarGradientNorm g D x ≤ b * (D.scalarCurvature x) ^ (3 / 2 : ℝ)
  laplacian_bound : ∃ b : ℝ, b < C ∧ ∀ x ∈ carrier,
    |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤ b * (D.scalarCurvature x) ^ 2



theorem CapQuantitativeData.nonempty_of_pointwise_radius
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (C : ℝ)
    (carrier core : Set M)
    (hscalar : ∀ x ∈ carrier, 0 < D.scalarCurvature x)
    (hdiameter : intrinsicDiameter g carrier <
      ENNReal.ofReal (C * scalarCurvatureSupOn g D carrier ^ (-1 / 2 : ℝ)))
    (hratio : ∃ b : ℝ, b < C ∧ ∀ x ∈ carrier, ∀ y ∈ carrier,
      D.scalarCurvature y ≤ b * D.scalarCurvature x)
    (hvolume : calibratedMetricVolume g carrier <
      ENNReal.ofReal C * ENNReal.ofReal (scalarCurvatureSupOn g D carrier ^ (-3 / 2 : ℝ)))
    {b : ℝ} (hb : C⁻¹ < b)
    (hradius : ∀ x ∈ core, ∃ r : ℝ, 0 < r ∧
      scalarCurvatureSupOn g D (g.ball x r) = r⁻¹ ^ 2 ∧
      closure (g.ball x r) ⊆ carrier ∧ IsCompact (closure (g.ball x r)) ∧
      ENNReal.ofReal (b * r ^ 3) ≤ calibratedMetricVolume g (g.ball x r))
    (hgradient : ∃ b : ℝ, b < C ∧ ∀ x ∈ carrier,
      scalarGradientNorm g D x ≤ b * (D.scalarCurvature x) ^ (3 / 2 : ℝ))
    (hevolution : ∃ b : ℝ, b < C ∧ ∀ x ∈ carrier,
      |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤ b * (D.scalarCurvature x) ^ 2) :
    Nonempty (CapQuantitativeData g D C carrier core) := by
  classical
  let radius : M → ℝ := fun x => if hx : x ∈ core then (hradius x hx).choose else 1
  have hchosen (x : M) (hx : x ∈ core) :
      0 < radius x ∧ scalarCurvatureSupOn g D (g.ball x (radius x)) = (radius x)⁻¹ ^ 2 ∧
      closure (g.ball x (radius x)) ⊆ carrier ∧
      IsCompact (closure (g.ball x (radius x))) ∧
      ENNReal.ofReal (b * radius x ^ 3) ≤ calibratedMetricVolume g (g.ball x (radius x)) := by
    simpa only [radius, dif_pos hx] using (hradius x hx).choose_spec
  exact ⟨{
    scalar_pos := hscalar
    intrinsic_diameter_bound := hdiameter
    scalar_ratio := hratio
    volume_bound := hvolume
    core_radius := radius
    core_radius_pos := fun x hx => (hchosen x hx).1
    core_radius_eq := fun x hx => (hchosen x hx).2.1
    core_ball_subset := fun x hx => (hchosen x hx).2.2.1
    core_ball_compact := fun x hx => (hchosen x hx).2.2.2.1
    core_ball_volume_lower := ⟨b, hb, fun x hx => (hchosen x hx).2.2.2.2⟩
    gradient_bound := hgradient
    laplacian_bound := hevolution }⟩

end PoincareConjecture.SingularRegularLimit
