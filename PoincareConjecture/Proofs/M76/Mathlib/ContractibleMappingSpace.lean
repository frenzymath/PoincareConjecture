import Mathlib.Topology.Homotopy.Contractible

set_option autoImplicit false

open unitInterval

namespace ContinuousMap

theorem contractibleSpace_of_target (B Y : Type*) [TopologicalSpace B]
    [LocallyCompactSpace B] [TopologicalSpace Y] [ContractibleSpace Y] :
    ContractibleSpace C(B, Y) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic Y
  apply (contractible_iff_id_nullhomotopic C(B, Y)).mpr
  refine ⟨ContinuousMap.const B y, ⟨{
    toFun := fun z => ⟨fun b => H (z.1, z.2 b),
      H.continuous.comp (continuous_const.prodMk z.2.continuous)⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · apply continuous_of_continuous_uncurry
    exact H.continuous.comp (continuous_fst.fst.prodMk
      (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)))
  · intro f
    ext b
    exact H.apply_zero (f b)
  · intro f
    ext b
    exact H.apply_one (f b)

end ContinuousMap
