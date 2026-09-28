import PoincareConjecture.Proofs.M51.HalfOpenSlabData

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51Slab

variable (F : SurgeryFlowData.{u}) {a H : ℝ} (haH : a < H)
    (hI : Ico a H ⊆ F.time_domain)
    (hS : Disjoint F.surgery_times (Ioo a H))

theorem metric_smooth : RiemannianMetric.IsSmoothFamilyOn
    (metric F haH hI hS) (Ico a H) := by
  unfold RiemannianMetric.IsSmoothFamilyOn
  apply contMDiffOn_of_locally_contMDiffOn
  intro p hp
  let U : Set (ℝ × (F.slice a).carrier) := {q | q.1 < cutoff a H p.1}
  refine ⟨U, isOpen_Iio.preimage continuous_fst, lt_cutoff hp.1, ?_⟩
  have hf := (slabAt F haH hI hS p.1).flow.smooth
  unfold RiemannianMetric.IsSmoothFamilyOn at hf
  refine (hf.mono (t := (Ico a H ×ˢ univ) ∩ U) ?_).congr ?_
  · intro q hq
    exact ⟨⟨hq.1.1.1, hq.2.le⟩, mem_univ _⟩
  · intro q hq
    have hm : metric F haH hI hS q.1 = (slabAt F haH hI hS p.1).flow.metric q.1 :=
      metric_eq_closed F haH hI hS q.1 hq.1.1 _
        (cutoff_bounds haH p.1).1 (cutoff_bounds haH p.1).2 hq.2.le
    rw [hm]

theorem equation (t : ℝ) (ht : t ∈ Ico a H) (x : (F.slice a).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    HasDerivWithinAt (fun s => (metric F haH hI hS s).inner x v w)
      (-2 * (connection F haH hI hS t).ricci x v w) (Ico a H) t := by
  have hc : Icc a (cutoff a H t) ∈ 𝓝[Ico a H] t :=
    mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds (lt_cutoff ht)))
      (fun _ hs => ⟨hs.1.1, hs.2.le⟩)
  have he := (slabAt F haH hI hS t).flow.equation t
    ⟨ht.1, (lt_cutoff ht).le⟩ x v w
  apply (he.mono_of_mem_nhdsWithin hc).congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [self_mem_nhdsWithin, hc] with s hs hsc
  have hm : metric F haH hI hS s = (slabAt F haH hI hS t).flow.metric s :=
    metric_eq_closed F haH hI hS s hs _
      (cutoff_bounds haH t).1 (cutoff_bounds haH t).2 hsc.2
  rw [hm]

noncomputable def flow : RicciFlow 3 (F.slice a).carrier (Ico a H) where
  metric := metric F haH hI hS
  connection := connection F haH hI hS
  interval := ordConnected_Ico
  nontrivial := by
    obtain ⟨b, hab, hbH⟩ := exists_between haH
    exact ⟨a, ⟨le_rfl, haH⟩, b, ⟨hab.le, hbH⟩, hab.ne⟩
  smooth := metric_smooth F haH hI hS
  equation := equation F haH hI hS

end PoincareConjecture.M51Slab
