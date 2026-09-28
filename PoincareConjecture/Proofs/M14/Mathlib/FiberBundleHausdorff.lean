import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Separation.Hausdorff










set_option autoImplicit false

open Bundle
open scoped Topology

namespace PoincareConjecture.M14




theorem fiberBundle_totalSpace_t2Space {B : Type*} (F : Type*) (E : B → Type*)
    [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [T2Space B] [T2Space F] :
    T2Space (TotalSpace F E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hne
  by_cases hbase : x.proj = y.proj
  · let e := trivializationAt F E x.proj
    have hx : x ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr
      (hbase ▸ mem_baseSet_trivializationAt F E x.proj)
    have he : e x ≠ e y := fun h => hne (e.toOpenPartialHomeomorph.injOn hx hy h)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr he) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj F E).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) (FiberBundle.continuous_proj F E).continuousAt

end PoincareConjecture.M14
