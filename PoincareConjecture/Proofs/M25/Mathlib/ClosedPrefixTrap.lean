import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Ring.Real

set_option autoImplicit false

open Set

universe u

theorem ContinuousOn.mapsTo_uIcc_of_closed_prefix_trap
    {X : Type u} [TopologicalSpace X]
    {gamma : ℝ → X} {U K : Set X} {a b : ℝ}
    (hcont : ContinuousOn gamma (Set.uIcc a b))
    (hU : IsOpen U) (hK : IsClosed K)
    (hstart : gamma a ∈ U)
    (hguard : K ∩ gamma '' Set.uIcc a b ⊆ U)
    (htrap : ∀ t ∈ Set.uIcc a b,
      Set.MapsTo gamma (Set.uIcc a t) U → gamma t ∈ K) :
    Set.MapsTo gamma (Set.uIcc a b) U := by
  classical
  let I : Set ℝ := uIcc a b
  let E : Set ℝ := I ∩ gamma ⁻¹' Uᶜ
  let Z : Set ℝ := I ∩ gamma ⁻¹' K
  have hIclosed : IsClosed I := isClosed_Icc
  have hEclosed : IsClosed E :=
    hcont.preimage_isClosed_of_isClosed hIclosed hU.isClosed_compl
  have hZclosed : IsClosed Z :=
    hcont.preimage_isClosed_of_isClosed hIclosed hK
  have hEcompact : IsCompact E :=
    (show IsCompact I from isCompact_uIcc).of_isClosed_subset hEclosed inter_subset_left
  by_cases hE : E.Nonempty
  · exfalso
    rcases le_total a b with hab | hba
    · obtain ⟨t, ht⟩ := hEcompact.exists_isLeast hE
      have htI : t ∈ uIcc a b := ht.1.1
      have htab : t ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using htI
      have hat : a < t := by
        apply lt_of_le_of_ne htab.1
        intro h
        exact ht.1.2 (by simpa only [h] using hstart)
      have hprefix : Ico a t ⊆ Z := by
        intro r hr
        have hrI : r ∈ uIcc a b := by
          rw [uIcc_of_le hab]
          exact ⟨hr.1, hr.2.le.trans htab.2⟩
        refine ⟨hrI, htrap r hrI ?_⟩
        intro v hv
        have hvr : v ∈ Icc a r := by
          simpa only [uIcc_of_le hr.1] using hv
        by_contra hvout
        have hvI : v ∈ I := by
          change v ∈ uIcc a b
          rw [uIcc_of_le hab]
          exact ⟨hvr.1, hvr.2.trans (hr.2.le.trans htab.2)⟩
        have hvE : v ∈ E := ⟨hvI, hvout⟩
        exact (not_le_of_gt (hvr.2.trans_lt hr.2)) (ht.2 hvE)
      have htclosure : t ∈ closure (Ico a t) := by
        rw [closure_Ico hat.ne]
        exact ⟨hat.le, le_rfl⟩
      have htZ : t ∈ Z := closure_minimal hprefix hZclosed htclosure
      exact ht.1.2 (hguard ⟨htZ.2, ⟨t, htI, rfl⟩⟩)
    · obtain ⟨t, ht⟩ := hEcompact.exists_isGreatest hE
      have htI : t ∈ uIcc a b := ht.1.1
      have htba : t ∈ Icc b a := by
        simpa only [uIcc_of_ge hba] using htI
      have hta : t < a := by
        apply lt_of_le_of_ne htba.2
        intro h
        exact ht.1.2 (by simpa only [h] using hstart)
      have hprefix : Ioc t a ⊆ Z := by
        intro r hr
        have hrI : r ∈ uIcc a b := by
          rw [uIcc_of_ge hba]
          exact ⟨htba.1.trans hr.1.le, hr.2⟩
        refine ⟨hrI, htrap r hrI ?_⟩
        intro v hv
        have hvr : v ∈ Icc r a := by
          simpa only [uIcc_of_ge hr.2] using hv
        by_contra hvout
        have hvI : v ∈ I := by
          change v ∈ uIcc a b
          rw [uIcc_of_ge hba]
          exact ⟨(htba.1.trans hr.1.le).trans hvr.1, hvr.2⟩
        have hvE : v ∈ E := ⟨hvI, hvout⟩
        exact (not_le_of_gt (hr.1.trans_le hvr.1)) (ht.2 hvE)
      have htclosure : t ∈ closure (Ioc t a) := by
        rw [closure_Ioc hta.ne]
        exact ⟨le_rfl, hta.le⟩
      have htZ : t ∈ Z := closure_minimal hprefix hZclosed htclosure
      exact ht.1.2 (hguard ⟨htZ.2, ⟨t, htI, rfl⟩⟩)
  · intro t ht
    by_contra hout
    exact hE ⟨t, ht, hout⟩
