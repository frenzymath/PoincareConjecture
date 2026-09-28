import PoincareConjecture.Statements.M25NeckCapTopology
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapDispatch
import PoincareConjecture.Proofs.M25.AppA_21_Local.FiniteTubeStop
import PoincareConjecture.Proofs.M25.AppA_21_Local.ClosedRegionAssembly
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapSecondFullBoundary
import PoincareConjecture.Proofs.M25.AppA_21_Local.CylinderExteriorTail
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapSecondTubeTail
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapSecondEndTail
import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalProtectedRestart
import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalNegativeReturnCircle










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace M25



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


end PoincareConjecture
