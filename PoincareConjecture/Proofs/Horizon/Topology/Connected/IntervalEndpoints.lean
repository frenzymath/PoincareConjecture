import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas







noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

private theorem exists_interval_image_subset_component
    {K L : Set X} {q : X} {g : ℝ → X} (hg : Continuous g)
    (hL : range g ⊆ L) {t : ℝ} (ht : g t ∈ connectedComponentIn K q)
    (hlocal : ∃ W : Set X, IsOpen W ∧ g t ∈ W ∧ W ∩ L ⊆ K) :
    ∃ u v : ℝ, t ∈ Ioo u v ∧ g '' Ioo u v ⊆ connectedComponentIn K q := by
  obtain ⟨W, hW, htW, hWK⟩ := hlocal
  obtain ⟨u, v, htuv, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hW.preimage hg).mem_nhds htW)
  refine ⟨u, v, htuv, ?_⟩
  have hc := (isPreconnected_Ioo.image g hg.continuousOn).subset_connectedComponentIn
    (mem_image_of_mem g htuv) (show g '' Ioo u v ⊆ K from ?_)
  · rwa [← connectedComponentIn_eq ht] at hc
  · rintro x ⟨s, hs, rfl⟩
    exact hWK ⟨huv hs, hL (mem_range_self s)⟩




theorem inter_connectedComponentIn_eq_interval_endpoints
    [T1Space X] {K L B : Set X} {q z : X} (hKL : K ⊆ L) (hz : z ∉ K)
    {g : ℝ → X} (hg : Topology.IsEmbedding g) {a b : ℝ} (hab : a < b)
    (hcomponent : g '' Icc a b = connectedComponentIn K q)
    (hrange : range g = connectedComponentIn L q \ {z})
    (hlocal : ∀ x ∈ K \ B, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ∩ L ⊆ K)
    (hcontact : ∀ x ∈ B, ∃ d : ℝ, 0 < d ∧ ∃ f : ℝ → X,
      ContinuousOn f (Ioo (-d) d) ∧ f 0 = x ∧
      f '' Ioo (-d) d ⊆ L ∧ ∀ t ∈ Ioo (-d) d, f t ∈ K ↔ 0 ≤ t) :
    B ∩ connectedComponentIn K q = {g a, g b} := by
  have hL : range g ⊆ L := by
    rw [hrange]
    exact fun x hx => connectedComponentIn_subset L q hx.1
  have ha : g a ∈ connectedComponentIn K q := by
    rw [← hcomponent]
    exact mem_image_of_mem g ⟨le_rfl, hab.le⟩
  have hb : g b ∈ connectedComponentIn K q := by
    rw [← hcomponent]
    exact mem_image_of_mem g ⟨hab.le, le_rfl⟩
  have haB : g a ∈ B := by
    by_contra hn
    obtain ⟨u, v, huv, hsub⟩ := exists_interval_image_subset_component hg.continuous
      hL ha (hlocal (g a) ⟨connectedComponentIn_subset K q ha, hn⟩)
    obtain ⟨s, hus, hsa⟩ := exists_between huv.1
    have hs := hsub (mem_image_of_mem g (show s ∈ Ioo u v from ⟨hus, hsa.trans huv.2⟩))
    rw [← hcomponent] at hs
    obtain ⟨t, ht, heq⟩ := hs
    have hts := hg.injective heq
    exact (not_le_of_gt hsa) (hts ▸ ht.1)
  have hbB : g b ∈ B := by
    by_contra hn
    obtain ⟨u, v, huv, hsub⟩ := exists_interval_image_subset_component hg.continuous
      hL hb (hlocal (g b) ⟨connectedComponentIn_subset K q hb, hn⟩)
    obtain ⟨s, hbs, hsv⟩ := exists_between huv.2
    have hs := hsub (mem_image_of_mem g (show s ∈ Ioo u v from ⟨huv.1.trans hbs, hsv⟩))
    rw [← hcomponent] at hs
    obtain ⟨t, ht, heq⟩ := hs
    have hts := hg.injective heq
    exact (not_le_of_gt hbs) (hts ▸ ht.2)
  apply subset_antisymm
  · rintro x ⟨hxB, hx⟩
    obtain ⟨t, ht, rfl⟩ := hcomponent.symm ▸ hx
    by_cases hta : t = a
    · simp [hta]
    by_cases htb : t = b
    · simp [htb]
    have hti : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
      lt_of_le_of_ne ht.2 htb⟩
    obtain ⟨d, hd, f, hf, hf0, hfL, hfK⟩ := hcontact (g t) hxB
    have h0 : (0 : ℝ) ∈ Ioo (-d) d := ⟨neg_neg_of_pos hd, hd⟩
    have hft : f 0 ∈ connectedComponentIn L q := by
      rw [hf0]
      exact connectedComponentIn_mono q hKL hx
    have hfcomp : f '' Ioo (-d) d ⊆ connectedComponentIn L q := by
      have hh := (isPreconnected_Ioo.image f hf).subset_connectedComponentIn
        (mem_image_of_mem f h0) hfL
      rwa [← connectedComponentIn_eq hft] at hh
    obtain ⟨W, hW, hpre⟩ := hg.isInducing.isOpen_iff.mp (isOpen_Ioo : IsOpen (Ioo a b))
    have htW : g t ∈ W := by
      show t ∈ g ⁻¹' W
      rwa [hpre]
    have htz : g t ≠ z := by
      intro heq
      exact hz (heq ▸ connectedComponentIn_subset K q hx)
    have hfcont : ContinuousAt f 0 := hf.continuousAt (Ioo_mem_nhds h0.1 h0.2)
    have hn : {s : ℝ | s ∈ Ioo (-d) d ∧ f s ∈ W ∧ f s ≠ z} ∈ 𝓝 0 := by
      refine inter_mem (Ioo_mem_nhds h0.1 h0.2) ?_
      refine hfcont (inter_mem (hW.mem_nhds ?_) (isOpen_compl_singleton.mem_nhds ?_))
      · rwa [hf0]
      · simpa [hf0] using htz
    obtain ⟨u, v, huv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
    obtain ⟨s, hus, hs0⟩ := exists_between huv.1
    have hs := hsub (show s ∈ Ioo u v from ⟨hus, hs0.trans huv.2⟩)
    have hsrange : f s ∈ range g := by
      rw [hrange]
      exact ⟨hfcomp (mem_image_of_mem f hs.1), hs.2.2⟩
    obtain ⟨r, hr⟩ := hsrange
    have hrab : r ∈ Ioo a b := by
      rw [← hpre]
      change g r ∈ W
      rw [hr]
      exact hs.2.1
    have hsK : f s ∈ K := by
      apply connectedComponentIn_subset K q
      rw [← hcomponent]
      exact ⟨r, ⟨hrab.1.le, hrab.2.le⟩, hr⟩
    exact ((not_le_of_gt hs0) ((hfK s hs.1).mp hsK)).elim
  · intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · exact ⟨haB, ha⟩
    · rcases mem_singleton_iff.mp hx with rfl
      exact ⟨hbB, hb⟩

end Poincare.Topology
