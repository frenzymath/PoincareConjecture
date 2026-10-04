import PoincareLib.Topology.Manifold.NeckCap.Models
import PoincareLib.Topology.Manifold.Surgery.Event.Circle.CirclePullback
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareLib.Geometry.Manifold.Covering.LocalDiffeomorph

/-!
# The smooth carrier of the circle pullback

Lift the actual carrier's atlas along the pullback projection. The height
is smooth because it is locally an inverse branch of the exponential
composed with the original smooth projection.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- The pullback uses its actual subspace topology and the lifted atlas. -/
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

/-- The original projection, with the lifted carrier kept explicit. -/
def circlePullbackProjection (Q : GeneralizedSliceCarrier.{u})
    (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π) :
    (circlePullbackCarrier Q π hπ).carrier → Q.carrier := CirclePullback.projection π

/-- The actual height, with the lifted carrier kept explicit. -/
def circlePullbackHeight (Q : GeneralizedSliceCarrier.{u})
    (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π) :
    (circlePullbackCarrier Q π hπ).carrier → ℝ := CirclePullback.height π

variable (Q : GeneralizedSliceCarrier.{u})
  (π : Q.carrier → UnitCircle) (hπ : ContMDiff (𝓡 3) (𝓡 1) ∞ π)

/-- The unchanged pullback projection is a local diffeomorphism. -/
theorem circlePullback_projection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (circlePullbackProjection Q π hπ) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph
    (CirclePullback.projection_isLocalHomeomorph π hπ.continuous) (𝓡 3) ∞

/-- The actual real height is smooth in the lifted atlas. -/
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

end PoincareMT.M38
