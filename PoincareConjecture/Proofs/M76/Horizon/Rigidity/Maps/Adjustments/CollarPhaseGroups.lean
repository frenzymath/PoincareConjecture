import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.PhaseMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalPhaseMapGroups

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem hamiltonZeroCollarTangentialMap_pi1_injective
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : SimplicialComplex ℝ E) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0) (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (theta : C0) (H : J.space ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0))
    (hzero : ∀ x : J.space, c (x, 0) = H x)
    (hinj : ∀ x : hamiltonZeroCircleMap phi ⁻¹' {theta},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0), X0)) x))
    (x : J.space) :
    Function.Injective (FundamentalGroup.map
      (hamiltonZeroCollarTangentialMap phi J hr c hc) x) := by
  have heq : hamiltonZeroCollarTangentialMap phi J hr c hc =
      (hamiltonZeroPhaseMap phi theta).comp ⟨H, H.continuous⟩ := by
    apply ContinuousMap.ext
    intro y
    change ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
      (hamiltonZeroAmbientMap phi (c (y, 0)))).1 = _
    rw [hzero y]
    change (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
      (hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv (H y)))))).1 = _
    rw [hamiltonZeroAmbientEquiv.apply_symm_apply]
    rfl
  rw [heq, FundamentalGroup.map_comp]
  exact (hamiltonZeroPhaseMap_pi1_injective phi F theta (H x) (hinj (H x))).comp
    (H.fundamentalGroupMulEquiv x).injective

end PoincareConjecture.M76
