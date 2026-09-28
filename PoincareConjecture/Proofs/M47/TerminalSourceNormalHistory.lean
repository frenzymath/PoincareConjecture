import PoincareConjecture.Proofs.M47.TerminalSourceNormalSurgery
import PoincareConjecture.Proofs.M47.TerminalSourceRealizationHistory









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {S : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow S}
  (H : M33RegularHistoryData W) {C : GeneralizedSliceCarrier.{u}} {b Q τ : ℝ}
  (U : TopologicalSpace.Opens C.carrier)
  (htime : ∀ s ∈ Icc (-τ) 0, b + s / Q ∈ H.generalized.interval)
  (e : GeneralizedFlowCylinder H.generalized C b Q (Icc (-τ) 0) U)



noncomputable def terminalSourceNormal_historyCylinder :
    SurgeryFlowCylinder S C b Q (Icc (-τ) 0) U :=
  (H.cylinders_to_surgery C b Q (Icc (-τ) 0) U ordConnected_Icc U.isOpen htime e).choose



theorem terminalSourceNormal_historyCylinder_maps :
    let d := terminalSourceNormal_historyCylinder H U htime e
    (∀ s hs, (fun x : U => d.forward s hs x.val) = fun x : U =>
      H.history.forward (b + s / Q) (htime s hs) (e.forward s hs x.val)) ∧
    ∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
      d.pullbackInner s hs x v w = e.pullbackInner s hs x v w := by
  have hd := (H.cylinders_to_surgery C b Q (Icc (-τ) 0) U
    ordConnected_Icc U.isOpen htime e).choose_spec
  refine ⟨?_, hd.2⟩
  intro s hs
  funext x
  exact hd.1 s hs x.val x.property



theorem terminalSourceNormal_history_terminal_map (p0 : U)
    (h0 : (0 : ℝ) ∈ Icc (-τ) 0) :
    let j := terminalSourceNormal_terminalMap U p0
      (terminalSourceNormal_historyCylinder H U htime e) h0
    (⟨b, fun x : U => j x⟩ : (t : ℝ) × (U → (S.slice t).carrier)) =
      ⟨b + 0 / Q, fun x : U =>
        H.history.forward (b + 0 / Q) (htime 0 h0) (e.forward 0 h0 x.val)⟩ := by
  have hj := (terminalSourceNormal_terminal_map U p0
    (terminalSourceNormal_historyCylinder H U htime e) h0).2.2
  exact hj.trans (congrArg (fun f : U → (S.slice (b + 0 / Q)).carrier =>
    (⟨b + 0 / Q, f⟩ : (t : ℝ) × (U → (S.slice t).carrier)))
      ((terminalSourceNormal_historyCylinder_maps H U htime e).1 0 h0))




theorem terminalSourceNormal_regular_history
    (p0 : U) (h0 : (0 : ℝ) ∈ Icc (-τ) 0)
    (F : RicciFlow 3 U (Icc (-τ) 0))
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric 0).inner x v w = e.pullbackInner 0 h0 x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (hnorm : ∀ x : U, (F.connection 0).curvatureTensorNorm x =
      (S.connection (b + 0 / Q)).curvatureTensorNorm
        (H.history.forward (b + 0 / Q) (htime 0 h0) (e.forward 0 h0 x.val)) / Q)
    {A R r K v : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hr : 0 < r) (hv : 0 < v)
    (hAR : A ≤ R) (hAr : A + r ≤ R) :
    let j := terminalSourceNormal_terminalMap U p0
      (terminalSourceNormal_historyCylinder H U htime e) h0
    (S.metric b).ball (j p0) (6 * R / Real.sqrt Q) ⊆ range (fun x : U => j x) →
    (∀ z ∈ (S.metric b).ball (j p0) (5 * R / Real.sqrt Q),
      (S.connection b).curvatureTensorNorm z ≤ K * Q) →
    ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤
      calibratedMetricVolume (S.metric b) ((S.metric b).ball (j p0) (r / Real.sqrt Q)) →
    let ρ := RiemannianMetric.localInjectivityRadius 3 K R v
    0 < ρ ∧ ρ < R ∧ ∀ p ∈ (F.metric 0).ball p0 A,
      ∃ chart : TerminalSourceChart (F.metric 0) ρ, chart.centre = p ∧
        ∀ s : ℝ, 0 < s → s ≤ R →
          0 < RiemannianMetric.smallerBallVolumeBound 3 K R v s ∧
          ENNReal.ofReal (RiemannianMetric.smallerBallVolumeBound 3 K R v s) ≤
            calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) ∧
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) < ⊤ ∧
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p s) =
            ENNReal.ofReal (Real.sqrt Q ^ 3) * calibratedMetricVolume (S.metric b)
              ((S.metric b).ball (j p) (s / Real.sqrt Q)) := by
  let d := terminalSourceNormal_historyCylinder H U htime e
  have hd := terminalSourceNormal_historyCylinder_maps H U htime e
  apply terminalSourceNormal_surgery U p0 d h0 F _ _ hK hA hr hv hAR hAr
  · intro x v w
    exact (hmetric x v w).trans (hd.2 0 h0 x.val x.property _ _).symm
  · intro x
    have hx := congrFun (hd.1 0 h0) x
    exact (hnorm x).trans (congrArg (fun z =>
      (S.connection (b + 0 / Q)).curvatureTensorNorm z / Q) hx.symm)

end PoincareConjecture.M47
