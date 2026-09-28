import PoincareConjecture.Proofs.M47.BlowupControlsCapSurvival
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalAssembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {origin scale c : ℝ}
  {U V : Set (F.slice origin).carrier}



theorem cap_preterminal_retained_of_terminal_avoidance
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (f : SurgeryFlowCylinder F (F.slice origin) origin scale (Icc 0 c) V)
    (hc : 0 < c) (hU : IsOpen U) (hconnected : IsPreconnected U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    (based : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (basedF : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x)
    (y : (F.slice origin).carrier) (hyU : y ∈ U) (hyV : y ∈ V)
    (havoid : ∀ i, Disjoint (M44.cylinderTerminalChart e hU hT r hr hr' '' U)
      ((F.event (origin + c / scale) hT).necks i).neck.central_sphere) :
    ∀ x ∈ U, ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / scale) hT).retained_pre := by
  let event := F.event (origin + c / scale) hT
  let pre := fun x => (event.pre_identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)
  have hpre : IsPreconnected (pre '' U) :=
    e.preterminal_image_preconnected hconnected hT r hr hr'
  have havoidPre : ∀ i, Disjoint (pre '' U)
      (event.limit_identify.inverse '' (event.necks i).neck.central_sphere) :=
    M44.preterminal_neck_avoidance_of_terminal P hpinch e hU hT r hr hr'
      havoid r hr hr'
  have heq : e.forward r hr y = f.forward r ⟨hr.1, hr.2.le⟩ y := by
    apply M44.cylinder_forward_eq_of_initial e f hr.1
      (fun _ hs => ⟨hs.1, hs.2.trans_lt hr.2⟩)
      (fun _ hs => ⟨hs.1, hs.2.trans hr.2.le⟩) y hyU hyV
    exact eq_of_heq ((based _ y hyU).trans (basedF _ y hyV).symm)
  have hretained : pre y ∈ interior event.retained_pre := by
    dsimp only [pre]
    rw [heq]
    exact f.pre_retained_at_surgery c ⟨hc.le, le_rfl⟩ hT r ⟨hr.1, hr.2.le⟩ hr' y hyV
  intro x hx
  by_contra hnot
  have hall := event.all_lost_of_avoids_necks hpre havoidPre
    ⟨pre x, mem_image_of_mem pre hx, hnot⟩
  exact (hall (mem_image_of_mem pre hyU)) hretained



theorem cap_preterminal_retained_of_terminal_geometry
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    {K D k : ℝ} (hK : 0 < K) (hD : 0 < D) (hk : 0 < k)
    (O : SurgeryObservation F)
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    {start rNext deltaBar : ℝ}
    (hscales : SurgeryFixedScalesOn setup F O start rNext deltaBar)
    (hdelta : deltaBar ≤ M44.laterNeckRemovalCutoff.{u} hK hD hk)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (f : SurgeryFlowCylinder F (F.slice origin) origin scale (Icc 0 c) V)
    (hc : 0 < c) (hU : IsOpen U) (hconnected : IsPreconnected U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (htime : origin + c / scale ∈ surgeryObservationInterval O ∩ Ici start)
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    (based : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (basedF : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x)
    (y : (F.slice origin).carrier) (hyU : y ∈ U) (hyV : y ∈ V)
    (g0 : StandardInitialMetric) {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    (sphere : C(UnitTwoSphere, g0.metric.ball 0 R))
    (transport : C(g0.metric.ball 0 R, (F.event (origin + c / scale) hT).terminal.carrier))
    (himage : range transport = M44.cylinderTerminalChart e hU hT r hr hr' '' U)
    (hscalar : ∀ x, (F.event (origin + c / scale) hT).limit_connection.scalarCurvature
      (transport x) ≤ K / h ^ 2)
    (hdiam : ∀ x z, (F.event (origin + c / scale) hT).limit_metric.edist
      (transport x) (transport z) < ENNReal.ofReal (h * D))
    (hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (transport.comp sphere))
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) (transport.comp sphere) z))
    (hplane : ∀ z, ∀ u v : TangentSpace (𝓡 2) z,
      let map := transport.comp sphere
      let deriv := mfderiv (𝓡 2) (𝓡 3) map z
      0 < (F.event (origin + c / scale) hT).limit_metric.inner (map z) (deriv u) (deriv u) *
        (F.event (origin + c / scale) hT).limit_metric.inner (map z) (deriv v) (deriv v) -
          ((F.event (origin + c / scale) hT).limit_metric.inner (map z) (deriv u) (deriv v)) ^ 2 →
        k / h ^ 2 < (F.event (origin + c / scale) hT).limit_connection.sectionalCurvature
          (map z) (deriv u) (deriv v)) :
    ∀ x ∈ U, ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / scale) hT).retained_pre := by
  have havoid := M44.terminal_neck_avoidance_of_geometry hK hD hk O setup
    hscales hdelta hT htime g0 hR hh sphere transport hscalar hdiam hsmooth himm hplane
  apply cap_preterminal_retained_of_terminal_avoidance P hpinch e f hc hU hconnected
    hT r hr hr' based basedF y hyU hyV
  simpa only [himage] using havoid

end PoincareConjecture.M47
