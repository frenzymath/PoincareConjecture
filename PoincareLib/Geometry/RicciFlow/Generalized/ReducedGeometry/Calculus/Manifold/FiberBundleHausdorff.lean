import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorff total spaces of fiber bundles

The closed phase-equality argument in Morgan-Tian Lemma 6.18,
pp. 113-114, uses the Hausdorff topology of the actual velocity
bundle. Projection separates distinct base points; a common local
trivialization separates distinct vectors over the same base point.
-/

set_option autoImplicit false

open Bundle
open scoped Topology

namespace PoincareMT.M14

/-- A fiber bundle with Hausdorff base and model fiber has Hausdorff
total space. This justifies the closed phase-equality set used for
the uniqueness assertion of Lemma 6.18, pp. 113-114. -/
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

end PoincareMT.M14
