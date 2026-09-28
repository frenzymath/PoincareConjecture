import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.ParametrizedSurface
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.OriginalTargetPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.PhaseMap



set_option autoImplicit false
open Geometry

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_parametrized_PL_torus_covering
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (J : SimplicialComplex ℝ E) (h : (C0 × C0) ≃ₜ J.space)
    (theta : C0) (f : C(J.space, C0 × C0))
    (hf : Function.Injective (FundamentalGroup.map f (h 0)))
    (hparam : PolyhedralPLInCharts d
      (hamiltonZeroCollarPhaseTarget J ⟨h.symm, h.symm.continuous⟩ theta) J.space) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℤ) (g : C(J.space, C0 × C0)),
      A.det ≠ 0 ∧ IsCoveringMap g ∧
      (∀ x, g x = LinearTorus.affineIntegerMatrixMap (4 * (16 : ℝ)) A
        (f (h 0)) (h.symm x)) ∧
      Nonempty (f.HomotopyRel g {h 0}) ∧
      PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J g theta) J.space := by
  classical
  obtain ⟨A, g, hA, hg, hformula, H⟩ :=
    exists_parametrized_torus_covering (4 * (16 : ℝ)) (by norm_num) h f hf
  refine ⟨A, g, hA, hg, hformula, H, ?_⟩
  apply (hd.polyhedralPL_hamiltonZeroTargetAffine A (f (h 0)) hparam).congr
  intro x hx
  simp only [Function.comp_apply, hamiltonZeroCollarPhaseTarget, dif_pos hx]
  apply (Q0).injective
  rw [LinearTorus.hamiltonZeroTargetAffine_coordinates]
  simp only [Homeomorph.apply_symm_apply]
  exact Prod.ext (hformula ⟨x, hx⟩).symm rfl

end PoincareConjecture.M76
