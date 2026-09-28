import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Cap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.CarrierLift
import PoincareConjecture.Definitions.M26CanonicalNeighborhoods

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe v u

namespace PoincareConjecture

attribute [local instance] RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

namespace RicciFlow

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem metricHomothety_ulift {J : Set ℝ} (F : RicciFlow 3 M J) (t : ℝ) :
    MetricHomothety (F.metric t) (F.ulift.metric t)
      (Poincare.Manifold.uliftDiffeomorph (𝓡 3) M :
        Diffeomorph (𝓡 3) (𝓡 3) (ULift.{v} M) M ∞).symm 1 := by
  let e : Diffeomorph (𝓡 3) (𝓡 3) M (ULift.{v} M) ∞ :=
    (Poincare.Manifold.uliftDiffeomorph (𝓡 3) M).symm
  have hid : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  intro x a b
  change (F.pullbackDiffeomorph e.symm |>.metric t).inner (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x a) (mfderiv (𝓡 3) (𝓡 3) e x b) = _
  rw [pullbackDiffeomorph_inner]
  have hi := mfderiv_comp x (e.symm.mdifferentiable (by simp) (e x))
    (e.mdifferentiable (by simp) x)
  rw [hid, mfderiv_id] at hi
  have ha := congrArg (fun L => L a) hi
  have hb := congrArg (fun L => L b) hi
  change a = mfderiv (𝓡 3) (𝓡 3) e.symm (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x a) at ha
  change b = mfderiv (𝓡 3) (𝓡 3) e.symm (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x b) at hb
  rw [← ha, ← hb, e.symm_apply_apply, one_mul]

noncomputable def capFromUlift {J : Set ℝ} (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate ((F.ulift : RicciFlow 3 (ULift.{v} M) J).metric t)) :
    CapCertificate (F.metric t) :=
  A.pullbackSmall (F.metricHomothety_ulift t) (F.connection t)

@[simp] theorem capFromUlift_epsilon {J : Set ℝ} (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate ((F.ulift : RicciFlow 3 (ULift.{v} M) J).metric t)) :
    (F.capFromUlift t A).epsilon = A.epsilon := rfl

@[simp] theorem capFromUlift_constant {J : Set ℝ} (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate ((F.ulift : RicciFlow 3 (ULift.{v} M) J).metric t)) :
    (F.capFromUlift t A).cap_constant = A.cap_constant := rfl

@[simp] theorem capFromUlift_core {J : Set ℝ} (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate ((F.ulift : RicciFlow 3 (ULift.{v} M) J).metric t)) :
    (F.capFromUlift t A).core = ULift.up ⁻¹' A.core := rfl

end RicciFlow

namespace AncientKappaSolution

variable [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]

variable (K : AncientKappaSolution 3 M)

noncomputable def strongNeckFromUlift {t epsilon : ℝ}
    (N : StrongEvolvingNeck (K.ulift : AncientKappaSolution 3 (ULift.{v} M)) t epsilon) :
    StrongEvolvingNeck K t epsilon :=
  N.pullbackCarrier (Poincare.Manifold.uliftDiffeomorph (𝓡 3) M).symm
    (fun s _ => K.flow.metricHomothety_ulift s)

@[simp] theorem strongNeckFromUlift_center {t epsilon : ℝ}
    (N : StrongEvolvingNeck (K.ulift : AncientKappaSolution 3 (ULift.{v} M)) t epsilon) :
    (K.strongNeckFromUlift N).center = N.center.down := rfl

theorem noEmbeddedTrivialNormalProjectivePlane_ulift
    (hno : NoEmbeddedTrivialNormalProjectivePlane K) :
    NoEmbeddedTrivialNormalProjectivePlane
      (K.ulift : AncientKappaSolution 3 (ULift.{v} M)) := by
  rintro ⟨f, hf⟩
  exact hno ⟨Homeomorph.ulift ∘ f, Homeomorph.ulift.isOpenEmbedding.comp hf⟩

end AncientKappaSolution

end PoincareConjecture
