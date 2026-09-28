import PoincareConjecture.Proofs.M38.CanonicalRegions
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem cylinder_connected {U : Set M} (C : OpenCylinderModel U) :
    IsConnected U := by
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  let : ConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo zero_lt_one)
  let : ConnectedSpace U := C.homeomorph.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

theorem cylinder_not_compact {U : Set M} (C : OpenCylinderModel U) :
    ¬ IsCompact U := by
  intro hU
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let : CompactSpace (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) :=
    C.homeomorph.symm.compactSpace
  let : CompactSpace (Set.Ioo (0 : ℝ) 1) :=
    Function.Surjective.compactSpace
      (f := (Prod.snd : UnitTwoSphere × Set.Ioo (0 : ℝ) 1 → Set.Ioo (0 : ℝ) 1))
      continuous_snd Prod.snd_surjective
  have hinterval : IsCompact (Set.Ioo (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mpr inferInstance
  exact (not_le_of_gt zero_lt_one) (isCompact_Ioo_iff.mp hinterval)

theorem no_tube_containing_compact_component
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (x : M)
    (hx : IsCompact (connectedComponent x)) :
    IsEmpty (EpsilonTubeCertificate g (connectedComponent x)) := by
  refine ⟨fun T => ?_⟩
  have hmem : x ∈ T.carrier := T.contains_X mem_connectedComponent
  have heq : T.carrier = connectedComponent x :=
    Set.Subset.antisymm ((cylinder_connected T.cylinder).subset_connectedComponent hmem)
      T.contains_X
  exact cylinder_not_compact T.cylinder (heq.symm ▸ hx)

end PoincareConjecture.M38
