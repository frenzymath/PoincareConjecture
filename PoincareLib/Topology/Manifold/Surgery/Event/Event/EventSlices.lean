import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.LocalTheory
import Mathlib.Tactic.Linarith

/-!
# Late reference slices for Proposition 15.3

The canonical control is used after the actual disappearing-start time.
The preterminal diffeomorphisms retain the original stored reference slice.
No metric-surgery selection or new flow service is needed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

/-- The doubled accuracy bound implies the bound needed for the supplied
Appendix A theory, at the same uniform threshold. -/
theorem epsilon_le_threshold (N : RepairedNeckCapTopologyTheory.{u})
    (F : SurgeryFlowData.{u}) (h : 2 * F.parameters.epsilon ≤ N.epsilon₀) :
    F.parameters.epsilon ≤ N.epsilon₀ := by
  linarith [F.parameters.epsilon_pos]

/-- Every nonnegative time before an actual surgery lies in the flow domain. -/
theorem mem_time_domain_before_surgery
    (F : SurgeryFlowData.{u}) {T t : ℝ} (hT : T ∈ F.surgery_times)
    (ht : 0 ≤ t) (htT : t ≤ T) : t ∈ F.time_domain :=
  F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ⟨ht, htT⟩

/-- Strong disappearing control is available on an actual compact late slice.
This is the use of Assumption (6) in Proposition 15.3, pp. 357-358; the printed
proof calls it Assumption (5). -/
theorem exists_nonempty_late_slice
    (F : SurgeryFlowData.{u}) (hF : SurgeryFlowAdmissible F)
    (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
    ∃ t : Set.Ico (F.event T hT).tMinus T,
      (F.event T hT).disappearing_start < t.1 ∧
      t.1 ∈ F.time_domain ∧
      IsCompact (Set.univ : Set (F.slice t.1).carrier) ∧
      ∀ x : (F.slice (F.event T hT).tMinus).carrier,
        x ∉ interior (F.event T hT).retained_pre →
          SurgeryCanonicalControl F t.1 ((F.event T hT).pre_identify t x)
            F.parameters.epsilon F.parameters.C := by
  obtain ⟨t, ht, htT⟩ := exists_between (F.event T hT).disappearing_start_bounds.2
  have htpre : (F.event T hT).tMinus ≤ t :=
    ((F.event T hT).disappearing_start_bounds.1.trans ht).le
  have htdomain : t ∈ F.time_domain := mem_time_domain_before_surgery F hT
    ((F.event T hT).tMinus_nonnegative.trans htpre) htT.le
  refine ⟨⟨t, htpre, htT⟩, ht, htdomain, F.slices_compact t htdomain, ?_⟩
  exact hF.strong_disappearing T hT ⟨t, htpre, htT⟩ ht.le

/-- Strong vanishing control covers the entire stored pre-slice after transport
to a compact late slice. The eventual post-slice may be empty. -/
theorem exists_vanishing_late_slice
    (F : SurgeryFlowData.{u}) (hF : SurgeryFlowAdmissible F)
    (T : ℝ) (hT : T ∈ F.surgery_times) [IsEmpty (F.slice T).carrier] :
    ∃ t : Set.Ico (F.vanishing_event T hT).tMinus T,
      (F.vanishing_event T hT).disappearing_start < t.1 ∧
      t.1 ∈ F.time_domain ∧
      IsCompact (Set.univ : Set (F.slice t.1).carrier) ∧
      ∀ x : (F.slice (F.vanishing_event T hT).tMinus).carrier,
        SurgeryCanonicalControl F t.1 ((F.vanishing_event T hT).pre_identify t x)
          F.parameters.epsilon F.parameters.C := by
  obtain ⟨t, ht, htT⟩ :=
    exists_between (F.vanishing_event T hT).disappearing_start_bounds.2
  have htpre : (F.vanishing_event T hT).tMinus ≤ t :=
    ((F.vanishing_event T hT).disappearing_start_bounds.1.trans ht).le
  have htdomain : t ∈ F.time_domain := mem_time_domain_before_surgery F hT
    ((F.vanishing_event T hT).tMinus_nonnegative.trans htpre) htT.le
  refine ⟨⟨t, htpre, htT⟩, ht, htdomain, F.slices_compact t htdomain, ?_⟩
  exact hF.strong_vanishing T hT ⟨t, htpre, htT⟩ ht.le

end PoincareMT.M38
