import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m64_exists_first_exit_closed
    {X : Type*} [TopologicalSpace X] {q : ℝ → X} {A : ℝ} (hA : 0 < A)
    (hq : ContinuousOn q (Icc 0 A)) {K : Set X} (hK : IsClosed K)
    (hzero : q 0 ∈ K) (henter : ∀ᶠ t in 𝓝[>] (0 : ℝ), q t ∈ K)
    (hout : q A ∉ K) :
    ∃ b ∈ Ioo 0 A, q b ∈ frontier K ∧ MapsTo q (Icc 0 b) K := by
  obtain ⟨eta, heta, hprefix⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp henter
  let S := {t ∈ Icc (0 : ℝ) A | q t ∉ K}
  have hS : S.Nonempty := ⟨A, ⟨hA.le, le_rfl⟩, hout⟩
  have hbound : BddBelow S := ⟨0, fun _ ht => ht.1.1⟩
  let b := sInf S
  have hbl : min eta A ≤ b := le_csInf hS (by
    intro t ht
    by_contra hn
    have htlt : t < min eta A := lt_of_not_ge hn
    have htpos : 0 < t := lt_of_le_of_ne ht.1.1 (by
      intro heq
      exact ht.2 (heq ▸ hzero))
    exact ht.2 (hprefix ⟨htpos, htlt.trans_le (min_le_left _ _)⟩))
  have hbpos : 0 < b := (lt_min heta hA).trans_le hbl
  have hbA : b ≤ A := csInf_le hbound ⟨⟨hA.le, le_rfl⟩, hout⟩
  have hpre : MapsTo q (Ico 0 b) K := by
    intro t ht
    by_contra hnot
    exact ht.2.not_ge (csInf_le hbound ⟨⟨ht.1, ht.2.le.trans hbA⟩, hnot⟩)
  have hclpre : MapsTo q (Icc 0 b) K := by
    have hc : ContinuousOn q (closure (Ico 0 b)) := by
      rw [closure_Ico hbpos.ne]
      exact hq.mono (Icc_subset_Icc le_rfl hbA)
    have h := hpre.closure_of_continuousOn hc
    simpa only [closure_Ico hbpos.ne, hK.closure_eq] using h
  have hbK : q b ∈ K := hclpre ⟨hbpos.le, le_rfl⟩
  have hboutside : q b ∈ closure Kᶜ := by
    have hsub : closure S ⊆ Icc 0 A :=
      closure_minimal (fun _ ht => ht.1) isClosed_Icc
    have hmap : MapsTo q S Kᶜ := fun _ ht => ht.2
    exact hmap.closure_of_continuousOn (hq.mono hsub) (csInf_mem_closure hS hbound)
  refine ⟨b, ⟨hbpos, lt_of_le_of_ne hbA ?_⟩, ?_, hclpre⟩
  · intro heq
    exact hout (heq ▸ hbK)
  · rw [frontier_eq_closure_inter_closure, hK.closure_eq]
    exact ⟨hbK, hboutside⟩

end PoincareConjecture
