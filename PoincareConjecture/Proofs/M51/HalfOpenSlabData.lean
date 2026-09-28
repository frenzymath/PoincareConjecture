import PoincareConjecture.Proofs.M51.SlabCoherence









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Slab

noncomputable def cutoff (a H t : ℝ) : ℝ :=
  if t ∈ Set.Ico a H then (t + H) / 2 else (a + H) / 2

theorem cutoff_bounds {a H : ℝ} (haH : a < H) (t : ℝ) :
    a < cutoff a H t ∧ cutoff a H t < H := by
  classical
  unfold cutoff
  split_ifs with ht
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith

theorem lt_cutoff {a H t : ℝ} (ht : t ∈ Set.Ico a H) : t < cutoff a H t := by
  rw [cutoff, if_pos ht]
  linarith [ht.2]

variable (F : SurgeryFlowData.{u}) {a H : ℝ} (haH : a < H)
    (hI : Set.Ico a H ⊆ F.time_domain)
    (hS : Disjoint F.surgery_times (Set.Ioo a H))

noncomputable def slabAt (t : ℝ) : SurgeryRegularSlab F.slice F.metric a (cutoff a H t) :=
  closedSlab F hI hS (cutoff a H t) (cutoff_bounds haH t).1 (cutoff_bounds haH t).2

noncomputable def metric (t : ℝ) : RiemannianMetric 3 (F.slice a).carrier :=
  (slabAt F haH hI hS t).flow.metric t

noncomputable def connection (t : ℝ) : LeviCivitaData (metric F haH hI hS t) :=
  (slabAt F haH hI hS t).flow.connection t

noncomputable def identify (t : Set.Ico a H) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice a).carrier (F.slice t.1).carrier ∞ :=
  (slabAt F haH hI hS t).identify ⟨t.1, t.2.1, (lt_cutoff t.2).le⟩

theorem identify_eq_closed (t : Set.Ico a H) (b : ℝ) (hab : a < b) (hbH : b < H)
    (htb : t.1 ≤ b) :
    ⇑(identify F haH hI hS t) =
      (closedSlab F hI hS b hab hbH).identify ⟨t.1, t.2.1, htb⟩ :=
  closedSlab_identify_eq F hI hS _ _ (cutoff_bounds haH t).1 (cutoff_bounds haH t).2
    hab hbH t ⟨t.2.1, (lt_cutoff t.2).le⟩ ⟨t.2.1, htb⟩

theorem metric_eq_closed (t : ℝ) (ht : t ∈ Set.Ico a H)
    (b : ℝ) (hab : a < b) (hbH : b < H) (htb : t ≤ b) :
    metric F haH hI hS t = (closedSlab F hI hS b hab hbH).flow.metric t :=
  closedSlab_metric_eq F hI hS _ _ (cutoff_bounds haH t).1 (cutoff_bounds haH t).2
    hab hbH t ⟨ht.1, (lt_cutoff ht).le⟩ ⟨ht.1, htb⟩

theorem initial_identify (x : (F.slice a).carrier) :
    identify F haH hI hS ⟨a, le_rfl, haH⟩ x = x :=
  (slabAt F haH hI hS a).initial_identify x

theorem metric_pullback (t : Set.Ico a H) (x : (F.slice a).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric t.1).inner (identify F haH hI hS t x)
      (mfderiv (𝓡 3) (𝓡 3) (identify F haH hI hS t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify F haH hI hS t) x w) =
        (metric F haH hI hS t).inner x v w :=
  (slabAt F haH hI hS t).metric_pullback ⟨t.1, t.2.1, (lt_cutoff t.2).le⟩ x v w


theorem transport_compatibility (b c : ℝ) (hbc : b < c)
    (hJ : Set.Icc b c ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Set.Ioc b c))
    (s t : ℝ) (hs : s ∈ Set.Icc b c) (ht : t ∈ Set.Icc b c)
    (hs' : s ∈ Set.Ico a H) (ht' : t ∈ Set.Ico a H) (x : (F.slice a).carrier) :
    (F.regular_slabs b c hbc hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      (identify F haH hI hS ⟨s, hs'⟩ x) = identify F haH hI hS ⟨t, ht'⟩ x := by
  obtain ⟨d, hd, hdH⟩ := exists_between (max_lt hs'.2 ht'.2)
  have hsd : s < d := (le_max_left _ _).trans_lt hd
  have htd : t < d := (le_max_right _ _).trans_lt hd
  have had : a < d := hs'.1.trans_lt hsd
  rw [identify_eq_closed F haH hI hS ⟨s, hs'⟩ d had hdH hsd.le,
    identify_eq_closed F haH hI hS ⟨t, ht'⟩ d had hdH htd.le]
  have hc := F.slab_transport_coherent b c a d hbc hJ hfree had
    (fun _ hu => hI ⟨hu.1, hu.2.trans_lt hdH⟩)
    (hS.mono_right (show Set.Ioc a d ⊆ Set.Ioo a H from
      fun _ hu => ⟨hu.1, hu.2.trans_lt hdH⟩)) s t
    hs ht ⟨hs'.1, hsd.le⟩ ⟨ht'.1, htd.le⟩
    ((closedSlab F hI hS d had hdH).identify ⟨s, hs'.1, hsd.le⟩ x)
  simpa only [closedSlab, SurgeryRegularSlab.transport,
    Diffeomorph.symm_apply_apply] using hc

end PoincareConjecture.M51Slab
