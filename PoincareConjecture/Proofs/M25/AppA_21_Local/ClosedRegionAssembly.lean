import PoincareConjecture.Statements.M25NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}


theorem repairedData_of_two_cap_component
    (H : ConnectedNeckCapCover g) (C1 C2 : CapCertificate g)
    (kind : ClosedComponentKind)
    (hcomponent : Nonempty (ClosedComponentCertificate kind
      (C1.carrier ∪ C2.carrier)))
    (hcontains : H.X ⊆ C1.carrier ∪ C2.carrier)
    (hε1 : C1.epsilon = H.epsilon) (hε2 : C2.epsilon = H.epsilon)
    (hC1 : C1.cap_constant ≤ H.cap_constant)
    (hC2 : C2.cap_constant ≤ H.cap_constant) :
    Nonempty (RepairedNeckCapTopologyData g H) := by
  rcases hcomponent with ⟨component⟩
  exact ⟨{
    region := .twoCaps kind C1 C2 component rfl hcontains
    compatible := ⟨hε1, hε2, hC1, hC2⟩ }⟩


theorem repairedData_of_double_capped_tube_component
    (H : ConnectedNeckCapCover g) (D : DoubleCappedTubeCertificate g)
    (kind : ClosedComponentKind)
    (hcomponent : Nonempty (ClosedComponentCertificate kind D.carrier))
    (hcontains : H.X ⊆ D.carrier)
    (hε1 : D.cap₁.epsilon = H.epsilon)
    (hε2 : D.cap₂.epsilon = H.epsilon)
    (hεT : D.tube.epsilon = H.epsilon)
    (hC1 : D.cap₁.cap_constant ≤ H.cap_constant)
    (hC2 : D.cap₂.cap_constant ≤ H.cap_constant) :
    Nonempty (RepairedNeckCapTopologyData g H) := by
  rcases hcomponent with ⟨component⟩
  exact ⟨{
    region := .doubleCappedTube D kind component hcontains
    compatible := ⟨hε1, hε2, hεT, hC1, hC2⟩ }⟩

end PoincareConjecture
