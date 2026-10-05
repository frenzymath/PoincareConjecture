import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Finiteness.EventCount

/-!
Adapted from Mapher `PoincareMT/Proofs/M50/Sec17_2_NoAccumulation.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Compact-set finiteness of surgery times

Morgan-Tian Section 17.2, p. 411, concludes that surgery times cannot
accumulate in finite time. A horizon bound for the exact certificate
controls every compact set, whether or not its endpoints are in the domain.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.SurgeryFiniteness

/-- Finite horizon counts give compact-set finiteness for the same raw
flow and exact certificate (MT Section 17.2, p. 411; M50 derivation 01). -/
theorem surgery_times_inter_compact_finite
    (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F)
    (V : RepairedVolumeLossData F C) (K : Set ℝ) (hK : IsCompact K) :
    (F.surgery_times ∩ K).Finite := by
  obtain ⟨B, hB⟩ := hK.bddAbove
  apply (surgery_times_inter_Icc_finite F C V (max 0 B) (le_max_left _ _)).subset
  intro T hT
  exact ⟨hT.1, F.time_domain_nonnegative (F.surgery_times_subset hT.1),
    (hB hT.2).trans (le_max_right _ _)⟩

end PoincareMT.SurgeryFiniteness
