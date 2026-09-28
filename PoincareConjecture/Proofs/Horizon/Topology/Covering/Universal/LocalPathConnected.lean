module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.IsLocalHomeomorph

public section

namespace Poincare.Topology

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

theorem _root_.IsLocalHomeomorph.locallyPathConnectedSpace [LocallyPathConnectedSpace B]
    {p : E → B} (hp : IsLocalHomeomorph p) : LocallyPathConnectedSpace E := by
  constructor
  intro e
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨W, hWU, hWopen, heW⟩ := mem_nhds_iff.mp hU
  let φ := hp.localInverseAt e
  have hpe_source : p e ∈ φ.source := hp.apply_self_mem_localInverseAt_source
  have hsource : IsOpen (φ.source ∩ φ ⁻¹' W) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hWopen
  have hpe : p e ∈ φ.source ∩ φ ⁻¹' W := by
    refine ⟨hpe_source, ?_⟩
    simpa only [Set.mem_preimage, φ, hp.localInverseAt_apply_self] using heW
  obtain ⟨V, ⟨hVopen, hpeV, hVpath⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis (p e)).mem_iff.mp (hsource.mem_nhds hpe)
  refine ⟨φ '' V, ?_, hVpath.image' (φ.continuousOn_toFun.mono fun _ hv => (hVsub hv).1), ?_⟩
  · exact (φ.isOpen_image_of_subset_source hVopen
      (hVsub.trans Set.inter_subset_left)).mem_nhds ⟨p e, hpeV, by simp [φ]⟩
  · rintro z ⟨y, hyV, rfl⟩
    exact hWU (hVsub hyV).2

end Poincare.Topology
