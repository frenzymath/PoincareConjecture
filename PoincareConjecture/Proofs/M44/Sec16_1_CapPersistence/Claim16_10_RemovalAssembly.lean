import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_UniformNeckExclusion
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalAvoidance
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalCylinderScalar
import PoincareConjecture.Proofs.Ch01.CurvatureConnection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal ContinuousMap

universe u

namespace PoincareConjecture.M44




noncomputable def laterNeckRemovalCutoff {K D k : ℝ}
    (hK : 0 < K) (hD : 0 < D) (hk : 0 < k) : ℝ :=
  (exists_uniform_neck_exclusion_cutoff.{u} hK hD hk).choose



theorem laterNeckRemovalCutoff_pos {K D k : ℝ}
    (hK : 0 < K) (hD : 0 < D) (hk : 0 < k) :
    0 < laterNeckRemovalCutoff.{u} hK hD hk :=
  (exists_uniform_neck_exclusion_cutoff.{u} hK hD hk).choose_spec.1




theorem terminal_neck_avoidance_of_geometry
    {K D k : ℝ} (hK : 0 < K) (hD : 0 < D) (hk : 0 < k)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    {start rNext deltaBar : ℝ}
    (hscales : SurgeryFixedScalesOn setup F O start rNext deltaBar)
    (hdelta : deltaBar ≤ laterNeckRemovalCutoff.{u} hK hD hk)
    {tPlus : ℝ} (hT : tPlus ∈ F.surgery_times)
    [Nonempty (F.slice tPlus).carrier]
    (htime : tPlus ∈ surgeryObservationInterval O ∩ Ici start)
    (g0 : StandardInitialMetric) {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    (sphere : C(UnitTwoSphere, g0.metric.ball 0 R))
    (transport : C(g0.metric.ball 0 R, (F.event tPlus hT).terminal.carrier))
    (hscalar : ∀ x, (F.event tPlus hT).limit_connection.scalarCurvature
      (transport x) ≤ K / h ^ 2)
    (hdiam : ∀ x y, (F.event tPlus hT).limit_metric.edist (transport x) (transport y) <
      ENNReal.ofReal (h * D))
    (hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (transport.comp sphere))
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) (transport.comp sphere) z))
    (hplane : ∀ z, ∀ u v : TangentSpace (𝓡 2) z,
      let f := transport.comp sphere
      let Df := mfderiv (𝓡 2) (𝓡 3) f z
      0 < (F.event tPlus hT).limit_metric.inner (f z) (Df u) (Df u) *
        (F.event tPlus hT).limit_metric.inner (f z) (Df v) (Df v) -
          ((F.event tPlus hT).limit_metric.inner (f z) (Df u) (Df v)) ^ 2 →
        k / h ^ 2 < (F.event tPlus hT).limit_connection.sectionalCurvature
          (f z) (Df u) (Df v)) :
    ∀ i, Disjoint (range transport) ((F.event tPlus hT).necks i).neck.central_sphere := by
  intro i
  let event := F.event tPlus hT
  let N := (event.necks i).neck
  have hsmall : N.epsilon ≤ laterNeckRemovalCutoff.{u} hK hD hk := by
    change (event.necks i).neck.epsilon ≤ _
    rw [event.neck_delta]
    exact (hscales.delta_le tPlus htime).trans hdelta
  apply (exists_uniform_neck_exclusion_cutoff.{u} hK hD hk).choose_spec.2
    N hsmall g0 R h hR hh sphere transport
  · intro x
    rw [N.connection.scalarCurvature_eq event.limit_connection]
    exact hscalar x
  · exact hdiam
  · exact hsmooth
  · exact himm
  · intro z u v
    dsimp only
    intro hgram
    rw [N.connection.sectionalCurvature_eq event.limit_connection]
    exact hplane z u v hgram




theorem disappears_of_terminal_geometry
    (P : M44CapPersistencePredecessors.{u})
    {K D k : ℝ} (hK : 0 < K) (hD : 0 < D) (hk : 0 < k)
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    (O : SurgeryObservation F)
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    {start rNext deltaBar : ℝ}
    (hscales : SurgeryFixedScalesOn setup F O start rNext deltaBar)
    (hdelta : deltaBar ≤ laterNeckRemovalCutoff.{u} hK hD hk)
    {origin scale c : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hconnected : IsPreconnected U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (htime : origin + c / scale ∈ surgeryObservationInterval O ∩ Ici start)
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale))
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hlost : ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
        ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
            interior (F.event (origin + c / scale) hT).retained_pre)
    (g0 : StandardInitialMetric) {R h : ℝ} (hR : 0 < R) (hh : 0 < h)
    (sphere : C(UnitTwoSphere, g0.metric.ball 0 R))
    (transport : C(g0.metric.ball 0 R,
      (F.event (origin + c / scale) hT).terminal.carrier))
    (himage : range transport = cylinderTerminalChart e hU hT r hr hr' '' U)
    (hscalar : ∀ s (hs : s ∈ Ico (0 : ℝ) c), ∀ x ∈ U,
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K / h ^ 2)
    (hdiam : ∀ x y, (F.event (origin + c / scale) hT).limit_metric.edist
      (transport x) (transport y) < ENNReal.ofReal (h * D))
    (hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (transport.comp sphere))
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) (transport.comp sphere) z))
    (hplane : ∀ z, ∀ u v : TangentSpace (𝓡 2) z,
      let f := transport.comp sphere
      let Df := mfderiv (𝓡 2) (𝓡 3) f z
      0 < (F.event (origin + c / scale) hT).limit_metric.inner (f z) (Df u) (Df u) *
        (F.event (origin + c / scale) hT).limit_metric.inner (f z) (Df v) (Df v) -
          ((F.event (origin + c / scale) hT).limit_metric.inner (f z) (Df u) (Df v)) ^ 2 →
        k / h ^ 2 < (F.event (origin + c / scale) hT).limit_connection.sectionalCurvature
          (f z) (Df u) (Df v)) :
    SurgeryBallDisappearsAt F e (origin + c / scale) := by
  apply disappears_of_terminal_neck_avoidance P hpinch e hU hconnected hT r hr hr'
    hinitial hlost
  have hterminal (x : g0.metric.ball 0 R) :
      (F.event (origin + c / scale) hT).limit_connection.scalarCurvature (transport x) ≤
        K / h ^ 2 := by
    have hx : transport x ∈ cylinderTerminalChart e hU hT r hr hr' '' U := by
      rw [← himage]
      exact mem_range_self x
    obtain ⟨y, hy, heq⟩ := hx
    rw [← heq]
    exact cylinderTerminalChart_scalar_le P hpinch e hU hT r hr hr' hy
      (fun s hs => hscalar s hs y hy)
  simpa only [himage] using terminal_neck_avoidance_of_geometry hK hD hk O setup hscales
    hdelta hT htime g0 hR hh sphere transport hterminal hdiam hsmooth himm hplane

end PoincareConjecture.M44
