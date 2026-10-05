import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Protection.MarkedCrossingEssentiality
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.SphereClopen
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Spheres.OriginalSphereSimplyConnected
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Protection.ExteriorFrontierConnected

/-!
The index-one protected exterior has no spherical boundary component.
The original marked geometry constructs an essential boundary loop, while the
boundary is connected. These facts supply the boundary exclusion needed in
the exterior prime-reduction step of Hamilton, p. 67.
-/

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.eq_frontier_of_connected
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R)
    (hconn : IsConnected (frontier R)) (hS : S ⊆ frontier R) : S = frontier R := by
  let : PreconnectedSpace (frontier R) :=
    isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  have hclopen := s.isClopen_in_frontier he hS
  obtain ⟨x, hx⟩ := s.isConnected.nonempty
  have hu := hclopen.eq_univ ⟨⟨x, hS hx⟩, hx⟩
  apply Subset.antisymm hS
  intro y hy
  have hh : (⟨y, hy⟩ : frontier R) ∈ (Subtype.val : frontier R → X) ⁻¹' S :=
    hu.symm ▸ mem_univ _
  exact hh

theorem HamiltonMarkedProtectedBall.nonspherical_exterior_frontier
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ¬ Nonempty (ChartwisePLSphere e
      (frontier (closure (latticeHandleDomain ι κ L \ D)))) := by
  rintro ⟨s⟩
  obtain ⟨j, rim, hj, hji, hjE, hrim, hproper, hessential⟩ :=
    b.exists_original_exterior_essential_disk he hdim hi
  let : SimplyConnectedSpace (frontier (closure (latticeHandleDomain ι κ L \ D))) :=
    s.simplyConnectedSpace
  exact hessential (Subsingleton.elim _ _)

theorem HamiltonMarkedProtectedBall.no_sphere_in_exterior_frontier
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    {S : Set (LatticeHandleAmbient ι κ L)}
    (hS : S ⊆ frontier (closure (latticeHandleDomain ι κ L \ D))) :
    ¬ Nonempty (ChartwisePLSphere e S) := by
  rintro ⟨s⟩
  have hEq := s.eq_frontier_of_connected (b.plDomain_closed_complement he hdim hi)
    (b.isConnected_closed_complement_frontier he hdim hi) hS
  exact b.nonspherical_exterior_frontier he hdim hi ⟨hEq ▸ s⟩

end PoincareMT.M76
