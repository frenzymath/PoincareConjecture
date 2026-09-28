import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarChartTransfer











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0



noncomputable def hamiltonZeroHandleMap (h : C(X0, X0)) : C(H0, H0) :=
  ⟨fun x => hamiltonZeroAmbientEquiv (h (hamiltonZeroAmbientEquiv.symm x)),
    hamiltonZeroAmbientEquiv.continuous.comp
      (h.continuous.comp hamiltonZeroAmbientEquiv.symm.continuous)⟩



theorem hamiltonZeroAmbientMap_handle (h : C(X0, X0)) :
    hamiltonZeroAmbientMap (hamiltonZeroHandleMap h) = h := by
  apply ContinuousMap.ext
  intro x
  change hamiltonZeroAmbientEquiv.symm (hamiltonZeroAmbientEquiv
    (h (hamiltonZeroAmbientEquiv.symm (hamiltonZeroAmbientEquiv x)))) = h x
  rw [hamiltonZeroAmbientEquiv.symm_apply_apply,
    hamiltonZeroAmbientEquiv.symm_apply_apply]



theorem hamiltonZeroHandleMap_ambient (phi : C(H0, H0)) :
    hamiltonZeroHandleMap (hamiltonZeroAmbientMap phi) = phi := by
  apply ContinuousMap.ext
  intro x
  change hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm
    (phi (hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm x)))) = phi x
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply,
    hamiltonZeroAmbientEquiv.apply_symm_apply]



theorem hamiltonZeroHandleMap_domain (h : C(X0, X0)) :
    latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap h) =
      hamiltonZeroAmbientMapInDomain h := by
  rw [← hamiltonZeroAmbientMapInDomain_original, hamiltonZeroAmbientMap_handle]





noncomputable def hamiltonZeroHandleHomotopy (phi : C(H0, H0))
    (G : C(unitInterval × X0, X0))
    (hzero : ∀ y : X0, G (0, y) = hamiltonZeroAmbientMap phi y) :
    phi.HomotopyRel
      (hamiltonZeroHandleMap ⟨fun y => G (1, y),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩) B0 where
  toFun z := hamiltonZeroAmbientEquiv (G (z.1, hamiltonZeroAmbientEquiv.symm z.2))
  continuous_toFun := hamiltonZeroAmbientEquiv.continuous.comp
    (G.continuous.comp (continuous_fst.prodMk
      (hamiltonZeroAmbientEquiv.symm.continuous.comp continuous_snd)))
  map_zero_left x := by
    change hamiltonZeroAmbientEquiv (G (0, hamiltonZeroAmbientEquiv.symm x)) = phi x
    rw [hzero]
    change hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm
      (phi (hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm x)))) = phi x
    rw [hamiltonZeroAmbientEquiv.apply_symm_apply,
      hamiltonZeroAmbientEquiv.apply_symm_apply]
  map_one_left _ := rfl
  prop' := by
    intro _ x hx
    rw [hamiltonZeroHandleBoundary_eq_empty] at hx
    exact False.elim hx



theorem hamiltonZeroHandleHomotopy_apply (phi : C(H0, H0))
    (G : C(unitInterval × X0, X0))
    (hzero : ∀ y : X0, G (0, y) = hamiltonZeroAmbientMap phi y)
    (t : unitInterval) (x : H0) :
    hamiltonZeroHandleHomotopy phi G hzero (t, x) =
      hamiltonZeroAmbientEquiv (G (t, hamiltonZeroAmbientEquiv.symm x)) := rfl



theorem hamiltonZeroHandleHomotopy_fixed_image (phi : C(H0, H0))
    (G : C(unitInterval × X0, X0))
    (hzero : ∀ y : X0, G (0, y) = hamiltonZeroAmbientMap phi y)
    {S : Set X0}
    (hfixed : ∀ (t : unitInterval) (y : X0), y ∈ S →
      G (t, y) = hamiltonZeroAmbientMap phi y)
    (t : unitInterval) (x : H0) (hx : x ∈ hamiltonZeroAmbientEquiv '' S) :
    hamiltonZeroHandleHomotopy phi G hzero (t, x) = phi x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hamiltonZeroHandleHomotopy_apply, hamiltonZeroAmbientEquiv.symm_apply_apply,
    hfixed t y hy]
  change hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm
    (phi (hamiltonZeroAmbientEquiv y))) = phi (hamiltonZeroAmbientEquiv y)
  exact hamiltonZeroAmbientEquiv.apply_symm_apply _



theorem hamiltonZeroHandleHomotopy_fixed_exterior (phi : C(H0, H0))
    (G : C(unitInterval × X0, X0))
    (hzero : ∀ y : X0, G (0, y) = hamiltonZeroAmbientMap phi y)
    {U : Set X0}
    (hfixed : ∀ (t : unitInterval) (y : X0), y ∉ U →
      G (t, y) = hamiltonZeroAmbientMap phi y)
    (t : unitInterval) (x : H0) (hx : x ∉ hamiltonZeroAmbientEquiv '' U) :
    hamiltonZeroHandleHomotopy phi G hzero (t, x) = phi x := by
  have hy : hamiltonZeroAmbientEquiv.symm x ∉ U := by
    intro hy
    exact hx ⟨hamiltonZeroAmbientEquiv.symm x, hy,
      hamiltonZeroAmbientEquiv.apply_symm_apply x⟩
  rw [hamiltonZeroHandleHomotopy_apply, hfixed t _ hy]
  change hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm
    (phi (hamiltonZeroAmbientEquiv (hamiltonZeroAmbientEquiv.symm x)))) = phi x
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply,
    hamiltonZeroAmbientEquiv.apply_symm_apply]

end PoincareConjecture.M76
