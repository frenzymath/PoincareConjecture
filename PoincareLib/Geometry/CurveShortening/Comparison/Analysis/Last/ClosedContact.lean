import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Last contact of a continuous path with a closed set

Compactness selects the actual final contact, even when the contact set
has infinitely many components. This is the last-base-contact step in
MT Claim 19.40, pp. 470-471.
-/

set_option autoImplicit false

open Set

/-- An interior contact with a closed set, followed by a terminal point outside it, has a
greatest contact time strictly inside the interval. Source: MT Claim 19.40, pp. 470-471;
derivations/2026-09-27-minimal-contact-regularity.md, Section 6. -/
theorem m64ContinuousOn_exists_last_closed_contact
    {X : Type*} [TopologicalSpace X] {gamma : ℝ → X} {L : ℝ} {C : Set X}
    (hc : ContinuousOn gamma (Icc 0 L)) (hC : IsClosed C)
    (hend : gamma L ∉ C) (hcontact : ∃ t ∈ Ioo 0 L, gamma t ∈ C) :
    ∃ u ∈ Ioo 0 L, gamma u ∈ C ∧ ∀ t ∈ Ioc u L, gamma t ∉ C := by
  let S := Icc (0 : ℝ) L ∩ gamma ⁻¹' C
  obtain ⟨t, ht, htc⟩ := hcontact
  have htS : t ∈ S := ⟨Ioo_subset_Icc_self ht, htc⟩
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left
  obtain ⟨u, hu, hgreatest⟩ := hcompact.exists_isGreatest ⟨t, htS⟩
  have hu0 : 0 < u := ht.1.trans_le (hgreatest htS)
  have huL : u < L := lt_of_le_of_ne hu.1.2 (fun heq => hend (heq ▸ hu.2))
  refine ⟨u, ⟨hu0, huL⟩, hu.2, ?_⟩
  intro s hs hsc
  exact (not_le_of_gt hs.1) (hgreatest ⟨⟨hu0.le.trans hs.1.le, hs.2⟩, hsc⟩)
