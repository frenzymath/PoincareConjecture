import PoincareConjecture.Proofs.M38.SphericalCoverFilling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.DeckAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38



theorem exists_spaceform_sphere_filling
    (Q : GeneralizedSliceCarrier.{u}) (S : SurgeryPositiveSpaceform Q)
    (f : UnitTwoSphere → Q.carrier)
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (p : Q.carrier) (hp : p ∉ range f) :
    ∃ B : SurgeryBallEmbedding Q, frontier B.closedBall = range f := by
  classical
  let : CompactSpace Q.carrier := ⟨S.compact⟩
  let : ConnectedSpace Q.carrier := connectedSpace_iff_univ.mpr S.connected
  obtain ⟨c, hc, hsec⟩ := S.round
  let g := rescaledMetric S.metric c hc
  let D := rescaledMetric_connection S.metric S.connection c hc
  have hg : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0 →
      g.leviCivitaData.sectionalCurvature x v w = 1 := by
    intro x v w hgram
    have horiginal : S.metric.inner x v v * S.metric.inner x w w -
        (S.metric.inner x v w) ^ 2 ≠ 0 := by
      intro h
      apply hgram
      change (rescaledMetric S.metric c hc).inner x v v *
        (rescaledMetric S.metric c hc).inner x w w -
        ((rescaledMetric S.metric c hc).inner x v w) ^ 2 = 0
      simp only [rescaledMetric_inner]
      calc
        _ = c ^ 2 * (S.metric.inner x v v * S.metric.inner x w w -
          (S.metric.inner x v w) ^ 2) := by ring
        _ = 0 := by rw [h, mul_zero]
    have heq : g.leviCivitaData.sectionalCurvature x v w = D.sectionalCurvature x v w := by
      simp only [LeviCivitaData.sectionalCurvature, g.leviCivitaData.horizon_curvatureTensor_eq D]
      rfl
    rw [heq, rescaledMetric_sectionalCurvature,
      S.connection.sectionalCurvature_eq_of_orthonormal x c (hsec x) v w horiginal,
      inv_mul_cancel₀ hc.ne']
  obtain ⟨q, _, hsurj, hq, hmetric⟩ := exists_spherical_covering g hg
  let : Finite (orthogonalDeckGroup q) := orthogonalDeckGroup_finite q hq
  apply exists_surgeryBall_of_finite_spherical_cover Q q hq hsurj
    (fun a : orthogonalDeckGroup q => sphereMotion a.val) (fun _ _ => rfl)
    (orthogonalDeckGroup_map_smul q) (orthogonalDeckGroup_free q hq) ?_ f hf p hp
  intro y z hyz
  obtain ⟨a, ha⟩ := (orthogonalDeckGroup_orbit_iff g q hq hmetric y z).mp hyz
  exact ⟨a, ha.symm⟩

end PoincareConjecture.M38
