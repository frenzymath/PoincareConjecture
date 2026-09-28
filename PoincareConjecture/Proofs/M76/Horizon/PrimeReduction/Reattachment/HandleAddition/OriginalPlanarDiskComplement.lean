import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.RelativePlanarDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarSurfaceCarrierBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarSurfaceInteriorGerms

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_planar_disk_complement
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {B : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hproper : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0)
    {A U W : Set P2} (hA : IsFinitePLBallPair P2 A (U ∪ W))
    (hAK : A ⊆ K.space) (hUB : U ⊆ B) (hW : IsClosed W) :
    ∃ C : Set P2, IsCompact C ∧ A ∪ C = K.space ∧ A ∩ C = W := by
  have hproper' : ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ K.space ∩ B :=
    fun z hz => (hproper z hz).trans ⟨fun h => ⟨hz,h⟩,fun h => h.2⟩
  have hfront := s.planar_exterior_frontier_eq he K hK inter_subset_left
    p hp hpi hps hproper' hcross
  have hdis : Disjoint (K.space ∩ B) (interior K.space) := by
    rw [←hfront]
    exact disjoint_interior_frontier.symm
  have hUB' : U ⊆ K.space ∩ B :=
    fun x hx => ⟨hAK (hA.1 (Or.inl hx)),hUB hx⟩
  have hopen := isOpen_relative_planar_disk_of_connected_interior_germs hA hAK hUB' hW
    hdis (s.planar_exterior_connected_dense_interior_germs he K hK p hp hpi hps hproper' hcross)
  exact exists_closed_planar_disk_complement_of_relative_open
    (K.isCompact_space_of_finite hK) hA hAK hopen

end PoincareConjecture.M76
