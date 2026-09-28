import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.Capping.OpenCover

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_inclusion_homotopyEquiv_of_motion
    {X : Type*} [TopologicalSpace X] {S U : Set X} (hSU : S ⊆ U)
    (D : C(unitInterval × X, X)) (hzero : ∀ x, D (0, x) = x)
    (hS : ∀ t, MapsTo (fun x => D (t, x)) S S)
    (hU : ∀ t, MapsTo (fun x => D (t, x)) U U)
    (hend : MapsTo (fun x => D (1, x)) U S) :
    ∃ E : ContinuousMap.HomotopyEquiv S U, E.toFun = ContinuousMap.inclusion hSU := by
  let i : C(S, U) := ContinuousMap.inclusion hSU
  let r : C(U, S) := ⟨fun x => ⟨D (1, x), hend x.property⟩,
    (D.continuous.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  let HS : (ContinuousMap.id S).Homotopy (r.comp i) := {
    toFun := fun z => ⟨D (z.1, z.2), hS z.1 z.2.property⟩
    continuous_toFun := (D.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (hzero x)
    map_one_left := fun _ => rfl }
  let HU : (ContinuousMap.id U).Homotopy (i.comp r) := {
    toFun := fun z => ⟨D (z.1, z.2), hU z.1 z.2.property⟩
    continuous_toFun := (D.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (hzero x)
    map_one_left := fun _ => rfl }
  exact ⟨⟨i, r, ⟨HS.symm⟩, ⟨HU.symm⟩⟩, rfl⟩

theorem pathConnectedSpace_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (E : ContinuousMap.HomotopyEquiv X Y) :
    PathConnectedSpace Y := by
  classical
  let H := E.right_inv.some
  refine ⟨Nonempty.map E inferInstance, fun x y => ?_⟩
  exact ⟨(H.evalAt x).symm.trans
    (((PathConnectedSpace.somePath (E.invFun x) (E.invFun y)).map E.continuous).trans
      (H.evalAt y))⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
