import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Covering.SimplyConnected











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

open Poincare.Geometry.Riemannian.SpaceForm



theorem SurgeryPositiveSpaceform.nonempty_diffeomorph_threeSphere
    {C : GeneralizedSliceCarrier.{u}} (S : SurgeryPositiveSpaceform C)
    [SimplyConnectedSpace C.carrier] :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞) := by
  letI : CompactSpace C.carrier := isCompact_univ_iff.mp S.compact
  letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr S.connected
  obtain ⟨c, hc, hround⟩ := S.round
  let g₁ := rescaledMetric S.metric c hc
  let D₁ := rescaledMetric_connection S.metric S.connection c hc
  have hsec : ∀ (x : C.carrier) (u v : TangentSpace (𝓡 3) x),
      g₁.inner x u u * g₁.inner x v v - (g₁.inner x u v) ^ 2 ≠ 0 →
        g₁.leviCivitaData.sectionalCurvature x u v = 1 := by
    intro x u v hgram
    have hgram' : S.metric.inner x u u * S.metric.inner x v v -
        (S.metric.inner x u v) ^ 2 ≠ 0 := by
      intro hz
      apply hgram
      change (c * S.metric.inner x u u) * (c * S.metric.inner x v v) -
        (c * S.metric.inner x u v) ^ 2 = 0
      rw [show (c * S.metric.inner x u u) * (c * S.metric.inner x v v) -
          (c * S.metric.inner x u v) ^ 2 =
          c ^ 2 * (S.metric.inner x u u * S.metric.inner x v v -
            (S.metric.inner x u v) ^ 2) by ring, hz, mul_zero]
    have hconst := S.connection.sectionalCurvature_eq_of_orthonormal x c
      (fun a b => hround x a b) u v hgram'
    have heq : g₁.leviCivitaData.sectionalCurvature x u v =
        D₁.sectionalCurvature x u v := by
      simp only [LeviCivitaData.sectionalCurvature,
        g₁.leviCivitaData.horizon_curvatureTensor_eq D₁]
      rfl
    rw [heq, rescaledMetric_sectionalCurvature, hconst]
    field_simp
  obtain ⟨q, hq, hqsurj, hqlocal, _⟩ :=
    exists_spherical_covering g₁ hsec
  letI : PreconnectedSpace (UnitSphere 3) :=
    isPreconnected_iff_preconnectedSpace.mp
      (isConnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank (by simp))
        (0 : EuclideanSpace ℝ (Fin 4)) (by norm_num)).isPreconnected
  letI : Nonempty (UnitSphere 3) :=
    ⟨⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩⟩
  letI : LocallyPathConnectedSpace C.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier
  have hbij : Function.Bijective q :=
    Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected
      (isLocalHomeomorph_iff_isCoveringMap.mp hqlocal.isLocalHomeomorph)
  exact ⟨(hqlocal.diffeomorphOfBijective ⟨hbij.1, hbij.2⟩).symm⟩

end PoincareConjecture
