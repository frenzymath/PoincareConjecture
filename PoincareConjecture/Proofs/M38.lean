import PoincareConjecture.Proofs.M38.EventTopology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem rawLocalSurgeryTopology : RawLocalSurgeryTopologyTheory.{u} :=
  ⟨M38.exists_raw_local_surgery_topology_data⟩

theorem repairedLocalSurgeryTopology : RepairedLocalSurgeryTopologyTheory.{u} := by
  refine ⟨?_⟩
  intro N
  obtain ⟨epsilon₀, hpositive, hthreshold, hraw⟩ := rawLocalSurgeryTopology.topology N
  exact ⟨epsilon₀, hpositive, hthreshold,
    fun D hadmissible hepsilon => hraw D.flow hadmissible hepsilon⟩
end PoincareConjecture
