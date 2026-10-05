import PoincareLib.Topology.Manifold.NeckCap.Theory
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Closed.ClosedModelCapDispatch
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Finite.FiniteTubeStop
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Closed.ClosedRegionAssembly
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Cap.CapSecondFullBoundary
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Cylinder.CylinderExteriorTail
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Cap.CapSecondTubeTail
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Cap.CapSecondEndTail
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Local.LocalProtectedRestart
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Local.LocalNegativeReturnCircle

/-!
# The remaining local constructions for A.21

The local nonseparating and finite capped cases are explicit propositions.
The two-cap kind dispatch retains the topology services as hypotheses.
Morgan--Tian, Proposition A.21 and Claims A.23-A.24, printed pp. 508-514;
see the reviewed entry-assembly-adoption derivation of 2026-09-23.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

namespace M25

/-- The nonseparating local-center construction of MT A.21 Case II,
pp. 513-514. A local center set need not fill its ambient component. -/
def NonseparatingLocalInput : Prop :=
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      (∀ x ∈ H.X, ∃ N ∈ H.necks, N.center = x) →
      (∃ N ∈ H.necks, N.center ∈ H.X ∧ N.IsNonseparating) →
      Nonempty (RepairedNeckCapTopologyData g H)

/-- The closed-region construction for the literal finite capped stopping
tuple, MT A.21 Case I and Claims A.23-A.24, pp. 511-514. -/
def FiniteCappedLocalInput : Prop :=
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      ∀ (x : M), x ∈ H.X →
      (∃ C0 ∈ H.caps, x ∈ C0.core ∧
        (∀ C1 ∈ H.caps,
          ¬ (C0.carrier \ C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆
            C1.core)) ∧
        ∃ (b : ℤ) (D : BalancedNeckChain g C0.epsilon),
          0 ≤ b ∧ D.shape = ChainShape.finite 0 b ∧
          D.source_necks = insert C0.end_neck H.necks ∧ D.neck 0 = C0.end_neck ∧
          (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) ∧
          (∀ i ∈ D.shape.active, 0 < i →
            (D.neck i).center ∈ H.X \ C0.carrier) ∧
          (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
            closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
                (D.neck (i + 1)).carrier ∧
              closure ((D.neck (i + 1)).region
                  (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) ∧
          (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
            (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 C0.epsilon⁻¹) ∧
              (D.neck (i + 1)).center ∉ (D.neck i).carrier) ∧
          ∃ K : CappedTubeCertificate g,
            K.cap = C0 ∧ K.tube.epsilon = H.epsilon ∧ HEq K.tube.chain D ∧
            K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            K.carrier = C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
              y ∈ C1.core ∧ y ∉ K.carrier ∧
              y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹) ∧
              (K.carrier ∩ C1.boundary_sphere).Nonempty) →
      Nonempty (RepairedNeckCapTopologyData g H)

end M25


end PoincareMT
