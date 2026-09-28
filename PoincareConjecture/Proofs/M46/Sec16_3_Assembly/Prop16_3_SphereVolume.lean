import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.ModelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.Proofs.M46

open Poincare.Geometry.Riemannian.SpaceForm

noncomputable def canonicalSphereMetric : RiemannianMetric 2 UnitTwoSphere :=
  rescaledMetric (roundSphereMetric 2) 2 (by norm_num)

noncomputable def canonicalSphereConnection : LeviCivitaData canonicalSphereMetric :=
  rescaledMetric_connection (roundSphereMetric 2) (roundSphereMetric 2).leviCivitaData
    2 (by norm_num)

noncomputable def canonicalSphereVolumeFloor : ℝ :=
  roundCylinderCrossSectionArea.toReal / (2 * Real.pi + 1) ^ 2

theorem canonicalSphereVolumeFloor_pos : 0 < canonicalSphereVolumeFloor :=
  div_pos roundCylinderCrossSectionArea_toReal_pos (sq_pos_of_pos (by positivity))

theorem canonicalSphere_ricci_nonneg (x : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) x) : 0 ≤ canonicalSphereConnection.ricci x v v := by
  let g := roundSphereMetric 2
  let D := g.leviCivitaData
  have hplane (u w : TangentSpace (𝓡 2) x) : 0 ≤ D.curvatureTensor x u w u w := by
    rw [roundSphereMetric_curvatureTensor, g.symm x w u]
    apply sub_nonneg.mpr
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact real_inner_mul_inner_self_le u w
  change 0 ≤ (rescaledMetric_connection g D 2 (by norm_num)).ricci x v v
  rw [rescaledMetric_ricci]
  exact Finset.sum_nonneg fun i _ => hplane v (g.orthonormalBasis x i)

theorem canonicalSphere_large_ball (q : UnitTwoSphere) :
    canonicalSphereMetric.ball q (2 * Real.pi + 1) = univ := by
  apply eq_univ_of_forall
  intro y
  change canonicalSphereMetric.edist q y < ENNReal.ofReal (2 * Real.pi + 1)
  rw [canonicalSphereMetric, rescaledMetric_edist,
    roundSphereMetric_edist_eq_angle (by norm_num),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hangle : Real.arccos (1 - dist q y ^ 2 / 2) ≤ Real.pi :=
    Real.arccos_le_pi _
  have hmul := mul_le_mul_of_nonneg_left hangle (Real.sqrt_nonneg 2)
  have hpi := mul_le_mul_of_nonneg_right hsqrt Real.pi_pos.le
  linarith

theorem canonicalSphere_small_ball_volume (q : UnitTwoSphere) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (canonicalSphereVolumeFloor * a ^ 2) ≤
      roundCylinderCrossSectionVolumeMeasure (canonicalSphereMetric.ball q a) := by
  let R := 2 * Real.pi + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have haR : a ≤ R := ha1.trans (by dsimp [R]; linarith [Real.pi_pos])
  have h := canonicalSphereMetric.smallBall_volume_lower_bound_of_precompact_ball q
    (by norm_num : 1 ≤ 2) (by positivity : 0 < R + 1) (le_refl (0 : ℝ))
    isClosed_closure.isCompact canonicalSphereConnection
    (fun x _ v => by simpa using canonicalSphere_ricci_nonneg x v)
    ha haR (by linarith : R < R + 1)
  rw [show canonicalSphereMetric.ball q R = univ from canonicalSphere_large_ball q] at h
  have harea : canonicalSphereMetric.volumeMeasure univ = roundCylinderCrossSectionArea := rfl
  rw [harea, RiemannianMetric.modelVolume_zero_curvature (by norm_num : 1 ≤ 2),
    RiemannianMetric.modelVolume_zero_curvature (by norm_num : 1 ≤ 2)] at h
  have hw := RiemannianMetric.euclideanUnitBallVolume_pos 2
  have heq : (ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 2 * a ^ 2) /
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 2 * R ^ 2)) *
        roundCylinderCrossSectionArea =
      ENNReal.ofReal (canonicalSphereVolumeFloor * a ^ 2) := by
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hw (sq_pos_of_pos hR)),
      ← ENNReal.ofReal_toReal roundCylinderCrossSectionArea_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold canonicalSphereVolumeFloor
    change _ = roundCylinderCrossSectionArea.toReal / R ^ 2 * a ^ 2
    field_simp [hw.ne', hR.ne']
  rw [heq] at h
  exact h

end PoincareConjecture.Proofs.M46
