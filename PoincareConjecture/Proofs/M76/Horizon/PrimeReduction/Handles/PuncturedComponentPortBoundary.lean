import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.NonsphericalBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedComponentPortBoundary

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.lattice_punctured_component_port_boundary
    {ι κ α ν E : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hindex : Fintype.card ι ≤ 2)
    {f : LatticeHandleAmbient ι κ L → E}
    (c : MarkedSphereCut e (latticeHandleDomain ι κ L) ν)
    (K : SimplicialComplex ℝ E) (g : E → LatticeHandleAmbient ι κ L)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ latticeHandleDomain ι κ L, f x ∈ K.space ∧ g (f x) = x)
    {x : LatticeHandleAmbient ι κ L} (hx : x ∈ c.carrier)
    (hm : HasPuncturedSphereModel e f (connectedComponentIn c.carrier x)) :
    IsCompact (connectedComponentIn c.carrier x) ∧
      PLDomain e (connectedComponentIn c.carrier x) ∧
      IsConnected (connectedComponentIn c.carrier x) ∧
      Disjoint (connectedComponentIn c.carrier x) (frontier (latticeHandleDomain ι κ L)) ∧
      frontier (connectedComponentIn c.carrier x) =
        ⋃ j : {j : ν × Bool // c.ports j ⊆ connectedComponentIn c.carrier x}, c.ports j := by
  exact c.punctured_component_port_boundary
    (fun _ s => s.not_subset_latticeHandle_frontier L he hdim hindex)
    K g hg hgi hreal hx hm

end PoincareConjecture.M76
