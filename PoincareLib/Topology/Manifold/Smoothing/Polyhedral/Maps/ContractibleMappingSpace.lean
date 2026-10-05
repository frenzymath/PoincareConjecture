import Mathlib.Topology.Homotopy.Contractible

/-!
# Contracting a space of continuous parameter families

A contraction of the target induces a contraction of the compact-open
mapping space when the source is locally compact. This retains all
transverse-slice parameters in Cairns' core extension, pp. 804--805;
see M76 derivation 56.
-/

set_option autoImplicit false

open unitInterval

namespace ContinuousMap

/-- Contractibility of the target gives contractibility of its
continuous mapping space over any locally compact source, using
the compact-open topology. See Cairns p. 804 and M76 derivation 56. -/
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
