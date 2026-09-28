import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModelBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RelativeComponentBoundary
import PoincareConjecture.Proofs.M76.Wall.SphericalFrontierFilling









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.punctured_component_port_boundary
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {f : X → E}
    (c : MarkedSphereCut e R κ)
    (hboundary : ∀ (S : Set X), ChartwisePLSphere e S → ¬ S ⊆ frontier R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    {x : X} (hx : x ∈ c.carrier)
    (hm : HasPuncturedSphereModel e f (connectedComponentIn c.carrier x)) :
    IsCompact (connectedComponentIn c.carrier x) ∧
      PLDomain e (connectedComponentIn c.carrier x) ∧
      IsConnected (connectedComponentIn c.carrier x) ∧
      Disjoint (connectedComponentIn c.carrier x) (frontier R) ∧
      frontier (connectedComponentIn c.carrier x) =
        ⋃ j : {j : κ × Bool // c.ports j ⊆ connectedComponentIn c.carrier x}, c.ports j := by
  classical
  let C := connectedComponentIn c.carrier x
  have hCsub : C ⊆ c.carrier := connectedComponentIn_subset _ _
  have hCc : IsCompact C := isCompact_connectedComponentIn_of_mem c.compactCut hx
  let : LocallyPathConnectedSpace c.carrier := c.plCut.locallyPathConnectedSpace
  obtain ⟨U,hU,hCU⟩ := exists_open_inter_of_relative_open hCsub
    (isOpen_preimage_connectedComponentIn hx)
  have hCf : frontier C = C ∩ frontier c.carrier :=
    frontier_eq_inter_of_eq_inter_open c.plCut.closed hCc.isClosed hU hCU
  have hportOld : Disjoint (⋃ j, c.ports j) (frontier R) := by
    apply disjoint_left.mpr
    intro y hy hyR
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact hyR.2 (c.collarInterior j.1 (c.portClosure j hj))
  have hportsClosed : IsClosed (⋃ j, c.ports j) :=
    isClosed_iUnion_of_finite (fun j => (c.portPL j).compact_connected.1.isClosed)
  obtain ⟨n,S,sS,hSC,hSdis,hSf⟩ := hm.exists_boundary_spheres hCc.isClosed K g hg hgi
    (fun y hy => hreal y ((hCsub hy).1))
  have hSnew (i : Fin n) : S i ⊆ ⋃ j, c.ports j := by
    have hSfront : S i ⊆ frontier R ∪ ⋃ j, c.ports j :=
      (subset_iUnion S i).trans (hSf.symm.subset.trans
        (hCf.subset.trans (inter_subset_right.trans c.frontierCut.subset)))
    have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp
      (sS i).compact_connected.2.isPreconnected
      (frontier R) (⋃ j, c.ports j) isClosed_frontier hportsClosed hSfront
      (by rw [hportOld.symm.inter_eq, inter_empty])
    exact hsplit.resolve_left (hboundary (S i) (sS i))
  have haway : Disjoint C (frontier R) := by
    apply disjoint_left.mpr
    intro y hyC hyR
    have hyCf : y ∈ frontier C := hCf.symm.subset
      ⟨hyC, c.frontierCut.symm.subset (Or.inl hyR)⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hSf.subset hyCf)
    exact disjoint_left.mp hportOld (hSnew i hi) hyR
  obtain ⟨hcompact,hPL,hconnected,hfront⟩ := c.plCut.component_frontier_away_from_old_boundary
    c.compactCut c.ports c.portPL c.frontierCut hx haway
  exact ⟨hcompact,hPL,hconnected,haway,hfront⟩

end PoincareConjecture.M76
