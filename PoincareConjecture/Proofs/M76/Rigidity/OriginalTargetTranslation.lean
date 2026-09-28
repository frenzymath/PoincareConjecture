import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleMap










set_option autoImplicit false

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))




noncomputable def hamiltonZeroAmbientMap (phi : C(H0, H0)) : C(X0, X0) :=
  ⟨fun x => hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv x)),
    hamiltonZeroAmbientEquiv.symm.continuous.comp
      (phi.continuous.comp hamiltonZeroAmbientEquiv.continuous)⟩



theorem hamiltonZeroAmbientMap_circle (phi : C(H0, H0)) (x : X0) :
    ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
      (hamiltonZeroAmbientMap phi x)).2 = hamiltonZeroCircleMap phi x := by
  change (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
    (hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv x))))).2 =
      (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).2
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply]




noncomputable def hamiltonZeroTargetTranslation : C(ℝ × X0, X0) :=
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  ⟨fun z => Q.symm ((Q z.2).1, (Q z.2).2 + (z.1 : C0)),
    Q.symm.continuous.comp
      ((Q.continuous.comp continuous_snd).fst.prodMk
        ((Q.continuous.comp continuous_snd).snd.add
          ((AddCircle.continuous_mk' (4 * (16 : ℝ))).comp continuous_fst)))⟩




theorem hamiltonZeroTargetTranslation_coordinates (u : ℝ) (y : X0) :
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
      (hamiltonZeroTargetTranslation (u, y)) =
        (((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates) y).1,
          ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates) y).2 +
            (u : C0)) :=
  (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).apply_symm_apply _



theorem hamiltonZeroTargetTranslation_zero (y : X0) :
    hamiltonZeroTargetTranslation (0, y) = y := by
  apply (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).injective
  simpa only [AddCircle.coe_zero, add_zero] using
    hamiltonZeroTargetTranslation_coordinates 0 y





theorem hamiltonZeroTargetTranslation_mk (u : ℝ) (x : Fin 0 → ℝ)
    (v : Fin 3 → ℝ) :
    hamiltonZeroTargetTranslation (u, (x, QuotientAddGroup.mk v)) =
      (x, QuotientAddGroup.mk ![v 0, v 1, v 2 + u]) := by
  apply (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).injective
  rw [hamiltonZeroTargetTranslation_coordinates]
  change (((v 0 : C0), (v 1 : C0)), (v 2 : C0) + (u : C0)) =
    (((v 0 : C0), (v 1 : C0)), ((v 2 + u : ℝ) : C0))
  rw [AddCircle.coe_add]

end PoincareConjecture.M76
