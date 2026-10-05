import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.AmbientScalar
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.ModelScalar
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.RealizedCurvature

/-!
# Uniform scalar curvature control throughout a neck

The realized curvature modulus, numerical cylinder scalar and ambient
naturality give one epsilon threshold for normalized scalar control at
every point of every neck. This is the scalar part of Morgan--Tian
Lemma A.2, pp. 497-498, used in the scale comparison of Proposition A.11.
See the ambient-scalar-naturality derivation. No quantitative O(epsilon^2)
rate, graph theorem or axial-angle bound is asserted here.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.EpsilonNeck

/-- Lemma A.2, pp. 497-498: at one universal epsilon threshold, normalized
ambient scalar curvature is close to one throughout every retained neck. -/
theorem exists_normalized_scalar_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      |N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, s)) - 1| < α := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ := exists_realized_scalar_ricci_control.{u} hα
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon q s hs
  obtain ⟨h, D, V, hV, h0, hstrip, heq⟩ :=
    N.m25_exists_normalizedEuclideanCoefficients_realization q hs
  have hnear : h.euclideanCoefficients =ᶠ[𝓝 0] N.m25_normalizedEuclideanCoefficients q s :=
    Filter.mem_of_superset (hV.mem_nhds h0) heq
  have hscalar := (hcontrol N hepsilon q hs h D hnear).1
  rw [N.realization_scalar_eq q s h D hV h0 hstrip heq,
    roundCylinderEuclideanModelConnection_scalar_one] at hscalar
  exact hscalar

/-- The coordinate form of Lemma A.2 gives the same uniform estimate at
every ambient point of the carrier, with no coordinate choices in the result. -/
theorem exists_normalized_scalar_control_on_carrier {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ x ∈ N.carrier, |N.scale ^ 2 * N.connection.scalarCurvature x - 1| < α := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ := exists_normalized_scalar_control.{u} hα
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon x hx
  have h := hcontrol N hepsilon (N.coordinate_inverse x).1
    (N.coordinate_inverse_mem x hx).2
  rw [Prod.mk.eta, N.coordinate_map_coordinate_inverse hx] at h
  exact h

end PoincareMT.EpsilonNeck
