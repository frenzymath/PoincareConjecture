import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Spherical.Defs
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Spherical.RoundMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.DeckAction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_sphericalSpaceFormCertificate
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (C : CompactRoundShrinkingModel G) :
    Nonempty (M24SphericalSpaceFormCertificate G) := by
  classical
  let : CompactSpace M := C.compact
  obtain ⟨q, hqsmooth, hqsurj, hqlocal, hqmetric⟩ :=
    exists_spherical_covering C.unitMetric C.unitMetric_sectionalCurvature
  let : Finite (orthogonalDeckGroup q) := orthogonalDeckGroup_finite q hqlocal
  let Γ := ULift.{u} (orthogonalDeckGroup q)
  let : Fintype Γ := Fintype.ofFinite Γ
  refine ⟨{
    group := Γ
    group_finite := inferInstance
    group_structure := inferInstance
    representation := fun a => sphereMotionMatrix a.down.val
    representation_identity := sphereMotionMatrix_one
    representation_comp := fun a b => sphereMotionMatrix_mul a.down.val b.down.val
    representation_orthogonal := fun a => sphereMotionMatrix_orthogonal a.down.val
    representation_orientation := fun a => orthogonalDeckGroup_det_one q hqlocal a.down
    action := fun a x => a.down • x
    action_identity := fun x => one_smul (orthogonalDeckGroup q) x
    action_comp := fun a b x => mul_smul a.down b.down x
    action_representation := fun a x => orthogonalDeckGroup_action_representation q a.down x
    action_free := ?_
    action_smooth := fun a => orthogonalDeckGroup_contMDiff q a.down
    action_distance_preserving := fun a x y => orthogonalDeckGroup_dist_smul q a.down x y
    compact := C.compact
    quotient_map := q
    quotient_map_surjective := hqsurj
    quotient_map_smooth := hqsmooth
    quotient_map_local_diffeomorph := hqlocal
    quotient_fiber := ?_
    roundMetric := SphericalShrinkingMetric.metric
    roundConnection := SphericalShrinkingMetric.connection
    round := fun t _ => SphericalShrinkingMetric.round t
    round_inner := ?_
    quotient_metric := G.flow.metric
    quotient_connection := G.flow.connection
    quotient_metric_transport := ?_
    flow_metric_transport := fun _ _ _ _ _ => rfl
    flow_connection_transport := fun _ _ _ _ _ => rfl
  }⟩
  · intro a x ha
    apply ULift.ext
    exact orthogonalDeckGroup_free q hqlocal a.down x ha
  · intro x y
    rw [orthogonalDeckGroup_orbit_iff C.unitMetric q hqlocal hqmetric]
    exact ⟨fun ⟨a, ha⟩ => ⟨ULift.up a, ha⟩, fun ⟨a, ha⟩ => ⟨a.down, ha⟩⟩
  · intro t ht x v w
    rw [SphericalShrinkingMetric.inner t ht, roundSphereMetric_inner,
      RiemannianMetric.euclideanMetric_inner]
  · intro t ht x u v
    rw [SphericalShrinkingMetric.inner t ht]
    exact C.inner_pullback_eq_round_scale q hqmetric t ht x u v

end PoincareConjecture
