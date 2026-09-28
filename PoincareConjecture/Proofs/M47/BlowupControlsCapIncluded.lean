import PoincareConjecture.Proofs.M47.BlowupControlsCapWholeRetention
import PoincareConjecture.Proofs.M47.BlowupControlsCapEndpoint
import PoincareConjecture.Proofs.M47.BlowupControlsCapOrdinaryEndpoint
import PoincareConjecture.Proofs.M47.BlowupControlsCapClosedComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem exists_actualCap_included_comparison_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta : theta < 1) (A0 : ℝ) :
    ∃ A eta0 delta0 : ℝ, 0 < A ∧ A0 < A ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial),
      HEq S standard.flow → SurgeryFlowPinched F →
      ∀ (O : SurgeryObservation F) {constants : MetricSurgeryConstants}
        (setup : SurgeryControlSetup constants) {start rNext deltaBar : ℝ},
      SurgeryFixedScalesOn setup F O start rNext deltaBar → deltaBar ≤ delta0 →
      ∀ (t : ℝ) (hbirth : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hbirth).cap_count) (c : ℝ) (hc : 0 < c), c ≤ theta →
      ∀ (U V : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 c) U)
        (survivor : SurgeryFlowCylinder F (F.slice t) t
          ((F.parameters.h t)⁻¹ ^ 2) (Icc 0 c) V)
        (initial : SurgeryCapInitialComparison F t hbirth i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta e initial.chart → (F.parameters.h t) ^ 2 ≤ 1 →
      t + c / ((F.parameters.h t)⁻¹ ^ 2) ∈ surgeryObservationInterval O ∩ Ici start →
      (∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) →
      (∀ hs x, x ∈ V → HEq (survivor.forward 0 hs x) x) →
      ∀ y : (F.slice t).carrier, y ∈ U → y ∈ V →
      ∃ closed : SurgeryFlowCylinder F (F.slice t) t
          ((F.parameters.h t)⁻¹ ^ 2) (Icc 0 c) U,
        SurgeryCapFamilyComparison F S A eta closed initial.chart ∧
        (∀ hs x, x ∈ U → HEq (closed.forward 0 hs x) x) ∧
        (∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Icc 0 c) x,
          closed.forward s hs' x = e.forward s hs x) ∧
        closed.forward c ⟨hc.le, le_rfl⟩ y =
          survivor.forward c ⟨hc.le, le_rfl⟩ y := by
  obtain ⟨A, eta0, delta0, hA, hA0, heta0, hetaHalf, hdelta0, retention⟩ :=
    exists_actualCap_whole_retention_cutoff.{u} P standard htheta0 htheta A0
  refine ⟨A, eta0, delta0, hA, hA0, heta0, hetaHalf, hdelta0, ?_⟩
  intro F hinitial S hS hpinch O constants setup start rNext deltaBar hscales hdelta
    t hbirth hn i c hc hctheta U V e survivor initial eta heta hetaSmall comparison hsmall
    htime based basedSurvivor y hyU hyV
  let q := capInitialPartialDiffeomorph initial
  have htarget : q.target = U := comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := htarget ▸ q.open_target
  have extended : ∃ d : ℝ, c < d ∧
      ∃ e' : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 d) U,
        ∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Ico 0 d) x,
          e'.forward s hs' x = e.forward s hs x := by
    by_cases hT : t + c / ((F.parameters.h t)⁻¹ ^ 2) ∈ F.surgery_times
    · let hnTop : Nonempty (F.slice (t + c / ((F.parameters.h t)⁻¹ ^ 2))).carrier :=
        ⟨survivor.forward c ⟨hc.le, le_rfl⟩ y⟩
      obtain ⟨r, hr, hr'⟩ := M44.exists_preterminal_parameter e.scale_pos hc
        (F.event (t + c / ((F.parameters.h t)⁻¹ ^ 2)) hT).tMinus_lt
      have hretained := retention F hinitial S hS hpinch O setup hscales hdelta
        t hbirth hn i c hc hctheta U V e survivor initial eta heta hetaSmall comparison hsmall
        hT hnTop htime r hr hr' based basedSurvivor y hyU hyV
      obtain ⟨d, hcd, _hdH, e', same, _endpoint⟩ :=
        exists_cap_cylinder_across_retained_endpoint P hpinch e hU hc O hT htime.1.2
          r hr hr' hretained
      exact ⟨d, hcd, e', same⟩
    · obtain ⟨d, hcd, _hdH, e', same⟩ :=
        exists_cap_cylinder_across_ordinary_endpoint e hU hc O htime.1.2 hT
      exact ⟨d, hcd, e', same⟩
  obtain ⟨d, hcd, e', same⟩ := extended
  obtain ⟨closed, closed_same, closed_comparison⟩ :=
    exists_closed_cap_comparison_of_continuation P hpinch S hA hc hcd
      (hctheta.trans_lt htheta) e e' initial same comparison
  have old_same (s : ℝ) (hs : s ∈ Ico 0 c) (hs' : s ∈ Icc 0 c) (x) :
      closed.forward s hs' x = e.forward s hs x :=
    (closed_same s hs' ⟨hs.1, hs.2.trans hcd⟩ x).trans
      (same s hs ⟨hs.1, hs.2.trans hcd⟩ x)
  have closed_based (hs : (0 : ℝ) ∈ Icc 0 c) (x) (hx : x ∈ U) :
      HEq (closed.forward 0 hs x) x :=
    (heq_of_eq (old_same 0 ⟨le_rfl, hc⟩ hs x)).trans (based _ x hx)
  refine ⟨closed, closed_comparison, closed_based, old_same, ?_⟩
  apply M44.cylinder_forward_eq_of_initial closed survivor hc.le Subset.rfl Subset.rfl y hyU hyV
  exact eq_of_heq ((closed_based _ y hyU).trans (basedSurvivor _ y hyV).symm)

end PoincareConjecture.M47
