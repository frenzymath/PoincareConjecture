import PoincareConjecture.Proofs.M47.GeneralizedBridgeGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem regular_history_compact_closure
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
    (hRegular : t ∉ F.surgery_times) (U : Set (H.generalized.slice t).carrier) :
    IsCompact (closure U) := by
  let : CompactSpace (F.slice t).carrier :=
    ⟨F.slices_compact t (H.history.time_subset ht)⟩
  let : CompactSpace (H.generalized.slice t).carrier :=
    (regular_history_slice_diffeomorph H t ht hRegular).toHomeomorph.symm.compactSpace
  exact isClosed_closure.isCompact

end PoincareConjecture.M47
