import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Basic










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M44



theorem isolated_surgery_neighborhood (F : SurgeryFlowData.{u})
    {t : ℝ} (ht : t ∈ F.time_domain) :
    ∃ a b : ℝ, a < t ∧ t < b ∧
      ∀ s ∈ F.surgery_times, s ∈ Ioo a b → s = t := by
  obtain ⟨d, hd, hfinite⟩ := F.surgery_times_locally_finite t ht
  have hcomp : ((F.surgery_times ∩ Ioo (t - d) (t + d)) \ {t})ᶜ ∈ 𝓝 t :=
    (hfinite.sdiff.isClosed.isOpen_compl).mem_nhds (by simp)
  have htime : Ioo (t - d) (t + d) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨a, b, ⟨hat, htb⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (inter_mem hcomp htime)
  refine ⟨a, b, hat, htb, ?_⟩
  intro s hs hsI
  have h := hsub hsI
  by_contra hne
  exact h.1 ⟨⟨hs, h.2⟩, hne⟩




theorem exists_surgery_free_right_interval (F : SurgeryFlowData.{u})
    {t H : ℝ} (ht : t ∈ F.time_domain) (htH : t < H) :
    ∃ b : ℝ, t < b ∧ b < H ∧ Disjoint F.surgery_times (Ioc t b) := by
  obtain ⟨a, z, hat, htz, hlocal⟩ := isolated_surgery_neighborhood F ht
  let b := (t + min H z) / 2
  have htmin : t < min H z := lt_min htH htz
  have htb : t < b := by dsimp [b]; linarith
  have hbmin : b < min H z := by dsimp [b]; linarith
  refine ⟨b, htb, hbmin.trans_le (min_le_left _ _), Set.disjoint_left.mpr ?_⟩
  intro s hs hsI
  have hst := hlocal s hs ⟨hat.trans hsI.1, hsI.2.trans_lt
    (hbmin.trans_le (min_le_right _ _))⟩
  exact (ne_of_gt hsI.1) hst




theorem exists_surgery_free_closed_neighborhood (F : SurgeryFlowData.{u})
    {l t h : ℝ} (ht : t ∈ F.time_domain) (hlt : l < t) (hth : t < h)
    (hnot : t ∉ F.surgery_times) :
    ∃ a b : ℝ, l < a ∧ a < t ∧ t < b ∧ b < h ∧
      Disjoint F.surgery_times (Icc a b) := by
  obtain ⟨u, v, hut, htv, hlocal⟩ := isolated_surgery_neighborhood F ht
  let a := (max l u + t) / 2
  let b := (t + min h v) / 2
  have hlow : max l u < t := max_lt hlt hut
  have hhigh : t < min h v := lt_min hth htv
  have hamax : max l u < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hbmin : b < min h v := by dsimp [b]; linarith
  refine ⟨a, b, (le_max_left _ _).trans_lt hamax, hat, htb,
    hbmin.trans_le (min_le_left _ _), Set.disjoint_left.mpr ?_⟩
  intro s hs hsI
  have hst := hlocal s hs ⟨((le_max_right _ _).trans_lt hamax).trans_le hsI.1,
    hsI.2.trans_lt (hbmin.trans_le (min_le_right _ _))⟩
  exact hnot (hst ▸ hs)

end PoincareConjecture.M44
