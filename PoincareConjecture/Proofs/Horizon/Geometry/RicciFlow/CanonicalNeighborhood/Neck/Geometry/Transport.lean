import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Tangent
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Volume











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

def roundCylinderVolumeMeasure : Measure RoundCylinderSpace := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  exact roundCylinderMetric.volumeMeasure

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def cylinderIntrinsicEDist (z w : RoundCylinderSpace) : ℝ≥0∞ := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  exact intrinsicEDist roundCylinderMetric N.cylinderDomain z w

theorem intrinsicEDist_bounds_of_quadratic
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbound : ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      a ^ 2 * EvolvingRoundCylinderMetric 0 z v v ≤
          roundCylinderPullback g N.coordinate_map z v v ∧
        roundCylinderPullback g N.coordinate_map z v v ≤
          b ^ 2 * EvolvingRoundCylinderMetric 0 z v v)
    {z w : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) (hw : w ∈ N.cylinderDomain) :
    ENNReal.ofReal a * N.cylinderIntrinsicEDist z w ≤
        intrinsicEDist g N.carrier (N.coordinate_map z) (N.coordinate_map w) ∧
      intrinsicEDist g N.carrier (N.coordinate_map z) (N.coordinate_map w) ≤
        ENNReal.ofReal b * N.cylinderIntrinsicEDist z w := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  have htangent := N.coordinate_tangentNorm_bounds ha.le hb.le hbound
  have hinverse := N.coordinate_inverse_tangentNorm_le ha (fun x hx v ↦ (htangent x hx v).1)
  constructor
  · have hh := g.intrinsicEDist_image_le_of_tangentNorm_le roundCylinderMetric
      N.carrier_open (N.coordinate_inverse_flat_smooth.of_le (by simp))
      N.coordinate_inverse_mem (inv_pos.mpr ha) hinverse (N.coordinate_map z) (N.coordinate_map w)
    rw [N.coordinate_inverse_coordinate_map hz, N.coordinate_inverse_coordinate_map hw] at hh
    change N.cylinderIntrinsicEDist z w ≤ _ at hh
    calc
      ENNReal.ofReal a * N.cylinderIntrinsicEDist z w ≤
          ENNReal.ofReal a * (ENNReal.ofReal a⁻¹ *
            intrinsicEDist g N.carrier (N.coordinate_map z) (N.coordinate_map w)) :=
        mul_le_mul_right hh _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le,
          mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one, one_mul]
  · exact roundCylinderMetric.intrinsicEDist_image_le_of_tangentNorm_le g
      N.cylinderDomain_open (N.coordinate_map_flat_smooth.of_le (by simp))
      (fun _ hx ↦ N.coordinate_map_mem hx) hb (fun x hx v ↦ (htangent x hx v).2) z w

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volume_bounds_of_quadratic
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbound : ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      a ^ 2 * EvolvingRoundCylinderMetric 0 z v v ≤
          roundCylinderPullback g N.coordinate_map z v v ∧
        roundCylinderPullback g N.coordinate_map z v v ≤
          b ^ 2 * EvolvingRoundCylinderMetric 0 z v v)
    {A : Set RoundCylinderSpace} (hA : MeasurableSet A) (hAN : A ⊆ N.cylinderDomain) :
    ENNReal.ofReal a ^ 3 * roundCylinderVolumeMeasure A ≤
        g.volumeMeasure (N.coordinate_map '' A) ∧
      g.volumeMeasure (N.coordinate_map '' A) ≤
        ENNReal.ofReal b ^ 3 * roundCylinderVolumeMeasure A := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  have htangent := N.coordinate_tangentNorm_bounds ha.le hb.le hbound
  have hinverse := N.coordinate_inverse_tangentNorm_le ha (fun x hx v ↦ (htangent x hx v).1)
  constructor
  · have hh := roundCylinderMetric.volumeMeasure_le_image_of_inverse_tangentNorm_le g
      N.coordinatePartialHomeomorph (N.coordinate_inverse_flat_smooth.of_le (by simp))
      (inv_pos.mpr ha) hinverse hA hAN
    change roundCylinderVolumeMeasure A ≤
      ENNReal.ofReal a⁻¹ ^ 3 * g.volumeMeasure (N.coordinate_map '' A) at hh
    calc
      ENNReal.ofReal a ^ 3 * roundCylinderVolumeMeasure A ≤
          ENNReal.ofReal a ^ 3 * (ENNReal.ofReal a⁻¹ ^ 3 *
            g.volumeMeasure (N.coordinate_map '' A)) := mul_le_mul_right hh _
      _ = _ := by rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul ha.le,
          mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one, one_pow, one_mul]
  · exact roundCylinderMetric.volumeMeasure_image_le_of_tangentNorm_le g
      N.coordinatePartialHomeomorph N.cylinderDomain_open subset_rfl
      (N.coordinate_map_flat_smooth.of_le (by simp)) hb (fun x hx v ↦ (htangent x hx v).2) hA hAN

end EpsilonNeck
end PoincareConjecture
