import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_StandardSphereMargin











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace



def StandardCylinderPatch.sphereInBall {length : ℝ} {center : E}
    (N : StandardCylinderPatch length center) (g0 : StandardInitialMetric) (R : ℝ)
    (hball : ∀ z : UnitTwoSphere,
      StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R) :
    C(UnitTwoSphere, g0.metric.ball 0 R) :=
  ⟨fun z => ⟨StandardCylinderPatch.sphereMap N z, hball z⟩,
    (StandardCylinderPatch.sphereMap N).continuous.subtype_mk hball⟩

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}

variable (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
  (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
  (hT : origin + c / scale ∈ F.surgery_times)
  [Nonempty (F.slice (origin + c / scale)).carrier]
  (r : ℝ) (hr : r ∈ Ico 0 c)
  (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
    (origin + c / scale))
  (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞)
  {g0 : StandardInitialMetric} {R : ℝ}
  (hsource : f.source = g0.metric.ball 0 R) (htarget : f.target = U)
  (hscalar : ∀ x ∈ U, ∃ K : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
    (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K)

include P hpinch hsource htarget hscalar




theorem terminal_birth_chart_source :
    (f.trans (cylinderTerminalChart e hU hT r hr hr')).source = g0.metric.ball 0 R := by
  ext x
  change (x ∈ f.source ∧ f x ∈ (cylinderTerminalChart e hU hT r hr hr').source) ↔ _
  rw [cylinderTerminalChart_source P hpinch e hU hT r hr hr' hscalar]
  constructor
  · exact fun hx => hsource ▸ hx.1
  · intro hx
    have hxf : x ∈ f.source := hsource.symm ▸ hx
    exact ⟨hxf, htarget ▸ f.map_source hxf⟩



theorem terminal_birth_chart_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (cylinderTerminalChart e hU hT r hr hr' ∘ f) (g0.metric.ball 0 R) := by
  have hq := (f.trans (cylinderTerminalChart e hU hT r hr hr')).contMDiffOn
  rwa [terminal_birth_chart_source P hpinch e hU hT r hr hr' f hsource htarget hscalar]
    at hq




theorem terminal_birth_chart_mfderiv_invertible {x : E} (hx : x ∈ g0.metric.ball 0 R) :
    (mfderiv (𝓡 3) (𝓡 3) (cylinderTerminalChart e hU hT r hr hr' ∘ f) x).IsInvertible := by
  let q := f.trans (cylinderTerminalChart e hU hT r hr hr')
  have hxq : x ∈ q.source := by
    rwa [terminal_birth_chart_source P hpinch e hU hT r hr hr' f hsource htarget hscalar]
  exact ⟨(q.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxq).mfderivToContinuousLinearEquiv
    (by simp), rfl⟩




noncomputable def terminalBirthBallTransport :
    C(g0.metric.ball 0 R, (F.event (origin + c / scale) hT).terminal.carrier) :=
  ⟨fun x => cylinderTerminalChart e hU hT r hr hr' (f x),
    (terminal_birth_chart_contMDiffOn P hpinch e hU hT r hr hr'
      f hsource htarget hscalar).continuousOn.domRestrict⟩




theorem terminalBirthBallTransport_range :
    range (terminalBirthBallTransport P hpinch e hU hT r hr hr'
      f hsource htarget hscalar) = cylinderTerminalChart e hU hT r hr hr' '' U := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, htarget ▸ f.map_source (hsource.symm ▸ x.property), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxt : x ∈ f.target := htarget.symm ▸ hx
    refine ⟨⟨f.symm x, hsource ▸ f.map_target hxt⟩, ?_⟩
    change cylinderTerminalChart e hU hT r hr hr' (f (f.symm x)) = _
    exact congrArg (cylinderTerminalChart e hU hT r hr hr') (f.right_inv hxt)



theorem terminalBirthBallTransport_sphere_smooth
    {length : ℝ} {center : E} (N : StandardCylinderPatch length center)
    (hball : ∀ z : UnitTwoSphere,
      StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R) :
    ContMDiff (𝓡 2) (𝓡 3) ∞
      ((terminalBirthBallTransport P hpinch e hU hT r hr hr'
        f hsource htarget hscalar).comp
          (StandardCylinderPatch.sphereInBall N g0 R hball)) := by
  let q := f.trans (cylinderTerminalChart e hU hT r hr hr')
  have hqsource := terminal_birth_chart_source P hpinch e hU hT r hr hr'
    f hsource htarget hscalar
  change ContMDiff (𝓡 2) (𝓡 3) ∞ (q ∘ StandardCylinderPatch.sphereMap N)
  intro z
  exact (q.contMDiffOn.contMDiffAt (q.open_source.mem_nhds
    (hqsource.symm ▸ hball z))).comp z (StandardCylinderPatch.contMDiff_sphere N z)




theorem terminalBirthBallTransport_sphere_immersion
    {length : ℝ} {center : E} (N : StandardCylinderPatch length center)
    (hball : ∀ z : UnitTwoSphere,
      StandardCylinderPatch.sphereMap N z ∈ g0.metric.ball 0 R)
    (z : UnitTwoSphere) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      ((terminalBirthBallTransport P hpinch e hU hT r hr hr'
        f hsource htarget hscalar).comp
          (StandardCylinderPatch.sphereInBall N g0 R hball)) z) := by
  let q := f.trans (cylinderTerminalChart e hU hT r hr hr')
  have hxq : StandardCylinderPatch.sphereMap N z ∈ q.source := by
    rw [terminal_birth_chart_source P hpinch e hU hT r hr hr' f hsource htarget hscalar]
    exact hball z
  change Function.Injective (mfderiv (𝓡 2) (𝓡 3)
    (q ∘ StandardCylinderPatch.sphereMap N) z)
  rw [mfderiv_comp z (q.mdifferentiableAt (by simp) hxq)
    ((StandardCylinderPatch.contMDiff_sphere N z).mdifferentiableAt (by simp))]
  exact (terminal_birth_chart_mfderiv_invertible P hpinch e hU hT r hr hr'
    f hsource htarget hscalar (hball z)).injective.comp
      (StandardCylinderPatch.sphere_immersion N z)

end PoincareConjecture.M44
