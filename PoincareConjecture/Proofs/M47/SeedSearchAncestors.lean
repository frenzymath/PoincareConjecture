import PoincareConjecture.Proofs.M47.PositiveHistoryAncestors

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

theorem seed_search_nonpositive_of_endpoint
    (e : SurgeryFlowCylinder F C origin scale I U) {x : C.carrier} (hx : x ∈ U)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b)
    (hend : ¬ SurgeryPositiveComponentAt F (origin + b / scale) (e.forward b hb x)) :
    ¬ SurgeryPositiveComponentAt F (origin + a / scale) (e.forward a ha x) := by
  intro hpos
  exact hend (M46.positive_component_cylinder_line e hx ha hb hab hpos)

theorem seed_search_nonpositive_of_cap_endpoint
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ}
    (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    (e : SurgeryFlowCylinder F C origin scale I U) {x : C.carrier} (hx : x ∈ U)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a < b)
    (hTJ : origin + b / scale ∈ J)
    (hT : origin + b / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + b / scale)).carrier]
    {i : Fin (F.event (origin + b / scale) hT).cap_count}
    (hcontact : (connectedComponent (e.forward b hb x) ∩
      ((F.event (origin + b / scale) hT).caps i).carrier).Nonempty) :
    ¬ SurgeryPositiveComponentAt F (origin + a / scale) (e.forward a ha x) := by
  let E := F.event (origin + b / scale) hT
  have hpre : scale * (E.tMinus - origin) < b := by
    have h := (lt_div_iff₀ e.scale_pos).mp
      (show E.tMinus - origin < b / scale by linarith [E.tMinus_lt])
    nlinarith
  obtain ⟨c, hc, hcb⟩ := exists_between (max_lt hab hpre)
  have hac : a < c := (le_max_left _ _).trans_lt hc
  have hpc : scale * (E.tMinus - origin) < c := (le_max_right _ _).trans_lt hc
  have hcI : c ∈ I := e.interval_connected.out ha hb ⟨hac.le, hcb.le⟩
  have hv : origin + c / scale ∈ Ico E.tMinus (origin + b / scale) := by
    constructor
    · have h := (le_div_iff₀ e.scale_pos).mpr
        (show (E.tMinus - origin) * scale ≤ c by nlinarith)
      linarith
    · have h := (div_lt_div_iff_of_pos_right e.scale_pos).mpr hcb
      linarith
  let q := (E.pre_identify ⟨origin + c / scale, hv⟩).symm (e.forward c hcI x)
  have hretained : q ∈ E.retained_pre :=
    interior_subset (e.pre_retained_at_surgery b hb hT c hcI hv x hx)
  have hchild : E.retention.map q = e.forward b hb x :=
    e.surgery_compatibility b hb hT c hcI hv x hx
  have hendpoint : e.forward c hcI x = E.pre_identify ⟨origin + c / scale, hv⟩ q :=
    ((E.pre_identify ⟨origin + c / scale, hv⟩).apply_symm_apply _).symm
  apply M47Positive.ancestor_nonpositive_of_retained_child_meets_cap
    hC F hpolicy hTJ hT e hx ha hcI hac.le hv q hendpoint hretained
  rwa [hchild]

end PoincareConjecture.Proofs.M47
