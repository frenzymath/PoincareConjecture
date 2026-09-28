import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.OneSheet.IdentityHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.HomeomorphInverseCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel
import Mathlib.Analysis.Convex.Topology











set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

variable {ι κ α β : Type*} [Fintype ι]
  (L : Submodule ℤ (κ → ℝ))



theorem latticeHandle_pathConnectedSpace : PathConnectedSpace (LatticeHandle ι κ L) := by
  let : PathConnectedSpace (closedBall (0 : ι → ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : ι → ℝ) 1).isPathConnected
        ⟨0, by simp⟩)
  let : PathConnectedSpace ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    (QuotientAddGroup.mk'_surjective L.toAddSubgroup).pathConnectedSpace
      QuotientAddGroup.continuous_mk
  infer_instance




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

end PoincareConjecture.M76
