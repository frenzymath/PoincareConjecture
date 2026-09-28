import PoincareConjecture.Proofs.M38.CirclePullback
import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

noncomputable def circlePullbackCarrier (Q : GeneralizedSliceCarrier.{u})
    (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π) :
    GeneralizedSliceCarrier.{u} := by
  let h := CirclePullback.projection_isLocalHomeomorph π hπ.continuous
  let := Poincare.Manifold.LocalHomeomorphLift.chartedSpace
    (H := EuclideanSpace ℝ (Fin 3)) h
  let := Poincare.Manifold.LocalHomeomorphLift.isManifold h (𝓡 3) ∞
  let : MeasurableSpace (CirclePullback π) := borel (CirclePullback π)
  let : BorelSpace (CirclePullback π) := ⟨rfl⟩
  let : SecondCountableTopology (Q.carrier × ℝ) := inferInstance
  let : SecondCountableTopology (CirclePullback π) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact {
    carrier := CirclePullback π
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := inferInstance
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := inferInstanceAs (T2Space {p : Q.carrier × ℝ // π p.1 = unitCircleExp p.2})
    t3Space := inferInstanceAs (T3Space {p : Q.carrier × ℝ // π p.1 = unitCircleExp p.2})
    secondCountable := inferInstance }

def circlePullbackProjection (Q : GeneralizedSliceCarrier.{u})
    (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π) :
    (circlePullbackCarrier Q π hπ).carrier → Q.carrier := CirclePullback.projection π

def circlePullbackHeight (Q : GeneralizedSliceCarrier.{u})
    (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π) :
    (circlePullbackCarrier Q π hπ).carrier → ℝ := CirclePullback.height π

variable (Q : GeneralizedSliceCarrier.{u})
  (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π)

theorem circlePullback_projection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (circlePullbackProjection Q π hπ) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph
    (CirclePullback.projection_isLocalHomeomorph π hπ.continuous) (𝓡 3) ∞

theorem circlePullback_height_smooth :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (circlePullbackHeight Q π hπ) := by
  intro a
  let h := isLocalDiffeomorph_unitCircleExp (CirclePullback.height π a)
  have hinverse : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ h.localInverse
      (π (CirclePullback.projection π a)) := by
    rw [CirclePullback.projection_height π a]
    exact h.localInverse_contMDiffAt
  have hs := hinverse.comp a
    ((hπ.comp (circlePullback_projection_localDiffeomorph Q π hπ).contMDiff) a)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(CirclePullback.continuous_height π).continuousAt.preimage_mem_nhds
    (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with b hb
  change CirclePullback.height π b = h.localInverse (π (CirclePullback.projection π b))
  rw [CirclePullback.projection_height π b, h.localInverse_left_inv hb]

end PoincareConjecture.M38
