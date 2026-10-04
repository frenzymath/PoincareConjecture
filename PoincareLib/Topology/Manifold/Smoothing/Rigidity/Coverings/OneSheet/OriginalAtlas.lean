import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.OneSheet.IdentityHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.HomeomorphInverseCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLatticeHandleModel
import Mathlib.Analysis.Convex.Topology

/-!
# The terminal covering in the original lattice-handle atlases

The retained identity homotopy makes a constructed covering one-sheeted.
Its actual inverse is PL in the original charts, by inversion of the finite
forward coordinate patches. Both literal boundary-relative homotopies are
retained. The geometric hierarchy must still construct the covering endpoint.
See Waldhausen 1968, Theorem 6.1, pp. 77--79.
-/

set_option autoImplicit false
open Set Metric

namespace PoincareMT.M76

variable {ι κ α β : Type*} [Fintype ι]
  (L : Submodule ℤ (κ → ℝ))

/-- Every marked lattice handle is path connected, using the convex disk
and the actual vector-space quotient. No lattice normalization is needed. -/
theorem latticeHandle_pathConnectedSpace : PathConnectedSpace (LatticeHandle ι κ L) := by
  let : PathConnectedSpace (closedBall (0 : ι → ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : ι → ℝ) 1).isPathConnected
        ⟨0, by simp⟩)
  let : PathConnectedSpace ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    (QuotientAddGroup.mk'_surjective L.toAddSubgroup).pathConnectedSpace
      QuotientAddGroup.continuous_mk
  infer_instance

/-- Turn an actual PL covering endpoint into the original relative rigidity
conclusion. Covering is the geometric input here; induced surjectivity and
inverse PL regularity are constructed internally. -/
theorem exists_lattice_handle_rigidity_of_covering
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (phi psi : C(LatticeHandle ι κ L, LatticeHandle ι κ L))
    (F : (ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel phi
      (latticeHandleBoundary ι κ L))
    (G : phi.HomotopyRel psi (latticeHandleBoundary ι κ L))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain ι κ L psi))
    (hcover : IsCoveringMap psi) :
    ∃ g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L,
      (∀ x, g x = psi x) ∧
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain ι κ L g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ (latticeHandleBoundary ι κ L)) ∧
      Nonempty ((ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel
        ⟨g, g.continuous⟩ (latticeHandleBoundary ι κ L)) := by
  let : PathConnectedSpace (LatticeHandle ι κ L) := latticeHandle_pathConnectedSpace L
  let H := F.trans G
  let g := hcover.homeomorphOfHomotopyRelId H
  have hg : (⟨g, g.continuous⟩ : C(LatticeHandle ι κ L, LatticeHandle ι κ L)) = psi := by
    apply ContinuousMap.ext
    intro x
    rfl
  have hPL : ChartwisePLMap e d
      ⟨latticeHandleHomeomorphInDomain ι κ L g,
        (latticeHandleHomeomorphInDomain ι κ L g).continuous⟩ := by
    change ChartwisePLMap e d (latticeHandleMapInDomain ι κ L ⟨g, g.continuous⟩)
    rwa [hg]
  refine ⟨g, fun _ => rfl, hPL.chartwisePLHomeomorph, ?_, ?_⟩
  · rw [hg]
    exact ⟨G⟩
  · rw [hg]
    exact ⟨H⟩

end PoincareMT.M76
