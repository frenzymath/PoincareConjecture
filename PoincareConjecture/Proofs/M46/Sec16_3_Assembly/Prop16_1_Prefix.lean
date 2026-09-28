import PoincareConjecture.Definitions.Ch16.ControlledSurgery









set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.Proofs.M46


theorem exists_epochEntry (i : ℕ) {t : ℝ}
    (ht : t ∈ Ico 0 (surgeryEpochStart i)) :
    ∃ j : Fin (i + 1), t ∈ surgeryEpochEntry j.val := by
  induction i with
  | zero => exact ⟨0, by simpa [surgeryEpochEntry] using ht⟩
  | succ i ih =>
    by_cases hti : t < surgeryEpochStart i
    · obtain ⟨j, hj⟩ := ih ⟨ht.1, hti⟩
      exact ⟨j.castSucc, hj⟩
    · refine ⟨Fin.last (i + 1), ?_⟩
      simpa [surgeryEpochEntry] using And.intro (le_of_not_gt hti) ht.2



theorem noncollapsedOn_mono {F : SurgeryFlowData.{u}} {J : Set ℝ}
    {kappa kappa' : ℝ} (h : SurgeryNoncollapsedOn F J kappa)
    (hle : kappa' ≤ kappa) : SurgeryNoncollapsedOn F J kappa' := by
  intro t ht htF x hpositive r hr hleR e hbase hcurv
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hle (pow_nonneg hr.le 3))).trans
      (h t ht htF x hpositive r hr hleR e hbase hcurv)



theorem prefix_noncollapsed {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (old : SurgeryPrefixControls p F O)
    {kappa : ℝ} (hle : kappa ≤ p.kappa (Fin.last p.i)) :
    SurgeryNoncollapsedOn F (surgeryObservationInterval O ∩ prefixFinalInterval p) kappa := by
  intro t ht htF x hpositive r hr hleR e hbase hcurv
  obtain ⟨j, hj⟩ := exists_epochEntry p.i ht.2
  have hjlast : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
  have hk : kappa ≤ p.kappa j :=
    hle.trans (p.kappa_antitone (show j.val ≤ (Fin.last p.i).val from hjlast))
  exact noncollapsedOn_mono (old.noncollapsed j hjlast) hk
    t ⟨ht.1, hj⟩ htF x hpositive r hr hleR e hbase hcurv

end PoincareConjecture.Proofs.M46
