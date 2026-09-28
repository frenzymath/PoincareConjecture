import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusInwardApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain

theorem m64Annulus_boundary_disk_sub_mem {x r : ℝ} {p : LoopPlane}
    (hp : p ∈ closedBall (annulusPoint x 0) r ∩ S) :
    p - annulusPoint x 0 ∈ closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} := by
  constructor
  · simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hp.1
  · have hpos := ((m64AnnulusInterior_coordinates p).mp hp.2).2.2.1
    change 0 ≤ (p - annulusPoint x 0) 1
    simpa [annulusPoint] using hpos.le

theorem m64Annulus_boundary_disk_preimage_ae {x r : ℝ}
    (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1) :
    (fun z : LoopPlane => z + annulusPoint x 0) ⁻¹'
      (closedBall (annulusPoint x 0) r ∩ S) =ᵐ[volume]
        (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} : Set LoopPlane) := by
  have hK : MeasurableSet (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) :=
    measurableSet_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hbase := (ae_restrict_iff' hK).mp (m64Annulus_halfDisk_ae_mem hx hP hr)
  filter_upwards [hbase] with z hz
  apply propext
  constructor
  · intro hmem
    change z ∈ closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
    simpa only [add_sub_cancel_right] using m64Annulus_boundary_disk_sub_mem hmem
  · intro hmem
    refine ⟨?_, hz hmem⟩
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hmem.1

theorem m64Annulus_boundary_disk_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x r : ℝ}
    (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1) (f : LoopPlane → E) :
    (∫ p in closedBall (annulusPoint x 0) r ∩ S, f p) =
      ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        f (z + annulusPoint x 0) := by
  have ht := (measurePreserving_add_right volume (annulusPoint x 0)).setIntegral_preimage_emb
    (Homeomorph.addRight (annulusPoint x 0)).measurableEmbedding f
    (closedBall (annulusPoint x 0) r ∩ S)
  exact ht.symm.trans (setIntegral_congr_set (m64Annulus_boundary_disk_preimage_ae hx hP hr))

theorem m64Annulus_boundary_disk_memLp {E : Type*} [NormedAddCommGroup E]
    {x r : ℝ} {f : LoopPlane → E}
    (hf : MemLp f 2 (volume.restrict
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))) :
    MemLp (fun p => f (p - annulusPoint x 0)) 2
      (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)) := by
  have hK : MeasurableSet (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) :=
    measurableSet_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hphys : MeasurableSet (closedBall (annulusPoint x 0) r ∩ S) :=
    measurableSet_closedBall.inter isOpen_interior.measurableSet
  have ht : MeasurePreserving (fun p : LoopPlane => p - annulusPoint x 0) volume volume := by
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure LoopPlane) (-annulusPoint x 0))
  exact (m64MeasurePreserving_memLp_restrict ht hK
    (ae_restrict_of_forall_mem hphys (fun _ hp => m64Annulus_boundary_disk_sub_mem hp)) hf).1

end PoincareConjecture
