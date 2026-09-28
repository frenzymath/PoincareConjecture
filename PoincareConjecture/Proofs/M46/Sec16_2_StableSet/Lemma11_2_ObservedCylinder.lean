import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_LowBallCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CutoffFloor
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ObservedWindow
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SmallRadiusAssembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46



theorem LowScalarCylinderProducer.cutoff_mono {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} {rNext cutoff smaller rho : ℝ}
    (produce : LowScalarCylinderProducer.{u} p rNext cutoff rho)
    (hsmall : smaller ≤ cutoff) :
    LowScalarCylinderProducer.{u} p rNext smaller rho := by
  intro F O inputs D hnew hlow
  exact produce F O (inputs.cutoff_mono hsmall) D hnew hlow




theorem lowScalarCylinder_of_observed_birth_bounds
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O) (D : NoncollapseTest F O)
    (hnew : surgeryEpochStart p.i ≤ D.time)
    (hcenter : (F.connection D.time).scalarCurvature D.center < rNext⁻¹ ^ 2)
    (hbirth : ∀ (t : ℝ) (hT : t ∈ F.surgery_times)
      [Nonempty (F.slice t).carrier], t ∈ surgeryObservationInterval O →
      surgeryEpochStart (p.i - 1) ≤ t →
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ x ∈ ((F.event t hT).caps i).carrier,
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature x) :
    Nonempty (LowScalarCylinder D (smallTestRadius B rNext)) := by
  have hwindow := observed_low_cylinder_window p inputs D hnew hB hr hrLast
  apply lowScalarCylinder_of_canonical_and_cap_floor P P44 S D inputs.pinched
    hB hBanalytic hr
    (hrLast.trans ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))))
    hcenter.le (fun t ht => O.interval_subset (hwindow ht).1)
    D.exists_later_observed_time
  · intro t ht x hhigh
    have h := inputs.canonical t (hwindow ht).1
      (O.interval_subset (hwindow ht).1) x hhigh
    simpa only [inputs.old.C_eq, hp.setup_eq] using h
  · intro t ht hT _ i x hx
    have hw := hwindow (Ioc_subset_Icc_self ht)
    have hdelta : F.parameters.delta t ≤ capScalarCutoff F.parameters.epsilon c rNext := by
      rw [inputs.old.epsilon_eq]
      exact (inputs.overlap t hw).trans hcutoff
    exact (cap_birth_floor_gt_four_inv_sq F hw.1.1 hc hr hdelta).trans_le
      (hbirth t hT hw.1 hw.2.1 i x hx)



theorem lowScalarCylinderProducer_of_birth_bounds
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    (hbirth : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      ObservedInputs p rNext cutoff F O →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ x ∈ ((F.event t hT).caps i).carrier,
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature x) :
    LowScalarCylinderProducer.{u} p rNext cutoff (smallTestRadius B rNext) := by
  intro F O inputs D hnew hcenter
  exact lowScalarCylinder_of_observed_birth_bounds P P44 S p hp hB hBanalytic hc
    hr hrLast hcutoff inputs D hnew hcenter (hbirth F O inputs)

end PoincareConjecture.Proofs.M46
