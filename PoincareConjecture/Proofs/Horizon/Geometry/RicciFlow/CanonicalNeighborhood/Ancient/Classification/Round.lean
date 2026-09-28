import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.RoundQuotient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TimeShift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional

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

theorem roundAncientSphericalSpaceForm
    (K : AncientKappaSolution 3 M) (hround : IsRoundAncientKappaSolution K) :
    Nonempty (M27SphericalSpaceFormFlowCertificate K) := by
  classical
  let : CompactSpace M := AncientKappaRoundness.compactSpace_of_isRoundMetricSlice
    (K.flow.connection 0) (K.complete 0 le_rfl) (hround 0 le_rfl)
  obtain ⟨c, hc, hsec⟩ := compactRound_sectionalCurvature (hround 0 le_rfl)
  let g := rescaledMetric (K.flow.metric 0) c hc
  let D := rescaledMetric_connection (K.flow.metric 0) (K.flow.connection 0) c hc
  have hg : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0 →
      g.leviCivitaData.sectionalCurvature x v w = 1 := by
    intro x v w hgram
    have hgram' : (K.flow.metric 0).inner x v v * (K.flow.metric 0).inner x w w -
        ((K.flow.metric 0).inner x v w) ^ 2 ≠ 0 := by
      intro h
      apply hgram
      dsimp only [g]
      simp only [rescaledMetric_inner]
      calc
        _ = c ^ 2 * ((K.flow.metric 0).inner x v v * (K.flow.metric 0).inner x w w -
          ((K.flow.metric 0).inner x v w) ^ 2) := by ring
        _ = 0 := by rw [h, mul_zero]
    have heq : g.leviCivitaData.sectionalCurvature x v w =
        D.sectionalCurvature x v w := by
      simp only [LeviCivitaData.sectionalCurvature, g.leviCivitaData.horizon_curvatureTensor_eq D]
      rfl
    rw [heq, rescaledMetric_sectionalCurvature,
      (K.flow.connection 0).sectionalCurvature_eq_of_orthonormal x c (hsec x) v w hgram',
      inv_mul_cancel₀ hc.ne']
  obtain ⟨q, hqsmooth, hqsurj, hqlocal, hqmetric⟩ := exists_spherical_covering g hg
  let : Finite (orthogonalDeckGroup q) := orthogonalDeckGroup_finite q hqlocal
  let Γ := ULift.{u} (orthogonalDeckGroup q)
  let : Fintype Γ := Fintype.ofFinite Γ
  let gs := fun t => (K.flow.metric t).pullbackOfLocalDiffeomorph q hqlocal
  refine ⟨{
    group := Γ
    group_finite := inferInstance
    group_structure := inferInstance
    representation := fun a => sphereMotionMatrix a.down.val
    representation_one := sphereMotionMatrix_one
    representation_mul := fun a b => sphereMotionMatrix_mul a.down.val b.down.val
    representation_orthogonal := fun a => sphereMotionMatrix_orthogonal a.down.val
    representation_orientation := fun a => orthogonalDeckGroup_det_one q hqlocal a.down
    action := fun a x => a.down • x
    action_representation := fun a x => orthogonalDeckGroup_action_representation q a.down x
    action_one := fun x => one_smul (orthogonalDeckGroup q) x
    action_mul := fun a b x => mul_smul a.down b.down x
    action_free := ?_
    action_smooth := fun a => orthogonalDeckGroup_contMDiff q a.down
    cover := q
    cover_surjective := hqsurj
    cover_local_diffeomorph := hqlocal
    cover_fibers := ?_
    metric := gs
    connection := fun t => (gs t).leviCivitaData
    round := ?_
    action_isometry := ?_
    metric_transport := fun _ _ _ _ _ => rfl
  }⟩
  · intro a x ha
    apply ULift.ext
    exact orthogonalDeckGroup_free q hqlocal a.down x ha
  · intro x y
    rw [orthogonalDeckGroup_orbit_iff g q hqlocal hqmetric]
    exact ⟨fun ⟨a, ha⟩ => ⟨ULift.up a, ha⟩, fun ⟨a, ha⟩ => ⟨a.down, ha⟩⟩
  · intro t ht
    obtain ⟨r, hr, hcurv⟩ := compactRound_sectionalCurvature (hround t ht)
    refine ⟨r, hr, fun x v w hv hw hvw => ?_⟩
    rw [(gs t).leviCivitaData.sectionalCurvature_eq_of_local_isometry
      (K.flow.connection t) isOpen_univ hqsmooth.contMDiffOn
      (fun _ _ _ _ => rfl) (Set.mem_univ x)]
    exact hcurv (q x) _ _ hv hw hvw
  · intro t _ a x v w
    have hcomp : q ∘ (fun y => a.down • y) = q :=
      funext (orthogonalDeckGroup_map_smul q a.down)
    have hderiv := mfderiv_comp x (hqsmooth.mdifferentiable (by simp)).mdifferentiableAt
      ((orthogonalDeckGroup_contMDiff q a.down).mdifferentiable (by simp)).mdifferentiableAt
    rw [hcomp] at hderiv
    change (K.flow.metric t).inner (q (a.down • x))
      ((mfderiv (𝓡 3) (𝓡 3) q (a.down • x))
        (mfderiv (𝓡 3) (𝓡 3) (fun y => a.down • y) x v))
      ((mfderiv (𝓡 3) (𝓡 3) q (a.down • x))
        (mfderiv (𝓡 3) (𝓡 3) (fun y => a.down • y) x w)) = _
    have hv := DFunLike.congr_fun hderiv v
    have hw := DFunLike.congr_fun hderiv w
    change mfderiv (𝓡 3) (𝓡 3) q x v =
      mfderiv (𝓡 3) (𝓡 3) q (a.down • x)
        (mfderiv (𝓡 3) (𝓡 3) (fun y => a.down • y) x v) at hv
    change mfderiv (𝓡 3) (𝓡 3) q x w =
      mfderiv (𝓡 3) (𝓡 3) q (a.down • x)
        (mfderiv (𝓡 3) (𝓡 3) (fun y => a.down • y) x w) at hw
    rw [← hv, ← hw]
    erw [orthogonalDeckGroup_map_smul q a.down x]
    rfl

end PoincareConjecture
