import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricComparison
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderImageVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

theorem controlled_cylinder_seed_image
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {origin c : ℝ} {U V : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hU : IsOpen U) (hbase : ∀ h y, y ∈ U → HEq (e.forward 0 h y) y)
    {K s volume : ℝ} (hs : s ∈ Ioc c 0) (hshort : 6 * K * (-s) ≤ 1 / 2)
    (hRm : ∀ t ht y, y ∈ U →
      (F.connection (origin + t / 1)).curvatureTensorNorm (e.forward t ht y) ≤ K)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hbuffer : closure V ⊆ U)
    (hvolume : ENNReal.ofReal volume ≤ calibratedMetricVolume (F.metric origin) V) :
    let A := e.forward s (Ioc_subset_Icc_self hs) '' V
    IsOpen A ∧ IsCompact (closure A) ∧
      closure A ⊆ m33RegularRegion F (origin + s / 1) ∧
      ENNReal.ofReal (volume / 8) ≤ calibratedMetricVolume (F.metric (origin + s / 1)) A := by
  dsimp only
  have hgeometry := cylinder_image_regular_compact_buffer e hU s
    (Ioc_subset_Icc_self hs) ⟨c, ⟨le_rfl, hs.1.le.trans hs.2⟩, hs.1⟩
    hV hcompact hbuffer
  refine ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2, ?_⟩
  have hmetric := fun y hy v => (based_cylinder_metric_comparison_two P hpinch e hU hbase
    hy v (Ioc_subset_Icc_self hs) hshort (fun t ht => hRm t ht y hy)).1
  have hbound := hvolume.trans (cylinder_image_volume_ge_eighth e hU (F.metric origin)
    s (Ioc_subset_Icc_self hs) hmetric hV (subset_closure.trans hbuffer))
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_ofNat]
  exact (ENNReal.div_le_iff' (by norm_num) (by norm_num)).mpr hbound

end PoincareConjecture.Proofs.M46
