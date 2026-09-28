import PoincareConjecture.Proofs.M35.CapGeometry.RadialStaticNeck










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)



theorem scalar_intrinsic_radial_center_unscaled (P : M35StandardCapPredecessors)
    (D : LeviCivitaData g) (q : UnitTwoSphere) (x : StandardCapSpace) :
    D.scalarCurvature (intrinsicSpatialInverse g hrotation hcomplete
      (radialArclength g ‖x‖ • q.val)) = D.scalarCurvature x := by
  rw [(rotational_scalar_edist_eq_axis P D hrotation _).1,
    intrinsic_radial_center_norm, ← (rotational_scalar_edist_eq_axis P D hrotation x).1]




noncomputable def scalarRadialNeck
    (atlas : StandardCylinderAtlas) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (q : UnitTwoSphere) (a b epsilon : ℝ)
    (hb : 0 < b) (he : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (hunit : Q * b ^ 2 = 1) (hinner : 0 < a - b * epsilon⁻¹)
    (hscalar : D.scalarCurvature (intrinsicSpatialInverse g hrotation hcomplete
      (a • q.val)) = Q)
    (hclose : RoundCylinderClose epsilon 0 (radialCylinderTensor
      (fun u => Q * intrinsicWarpingRadius g hrotation hcomplete (a + b * u) ^ 2) 1)) :
    StandardStaticNeck atlas g D epsilon := by
  let N := intrinsicRadialAnnulusPatch g hrotation hcomplete q a b epsilon⁻¹ hb
    (inv_pos.mpr he) hinner
  refine {
    epsilon_pos := he
    epsilon_lt_half := hehalf
    center := intrinsicSpatialInverse g hrotation hcomplete (a • q.val)
    scalar_pos := by rw [hscalar]; exact hQ
    patch := N
    close := ?_
  }
  change RoundCylinderClose epsilon 0 (fun z v w =>
    D.scalarCurvature (intrinsicSpatialInverse g hrotation hcomplete (a • q.val)) *
      roundCylinderPullback g N.coordinate z v w)
  rw [hscalar]
  let B := radialCylinderTensor
    (fun u => Q * intrinsicWarpingRadius g hrotation hcomplete (a + b * u) ^ 2) 1
  have heq : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = Q * roundCylinderPullback g N.coordinate z v w := by
    intro z hz v w
    have h := intrinsicRadialAnnulusPatch_pullback g hrotation hcomplete q a b epsilon⁻¹ hb
      (inv_pos.mpr he) hinner z hz v w
    have hraw : radialCylinderTensor
        (fun u => intrinsicWarpingRadius g hrotation hcomplete (a + b * u) ^ 2) b z v w =
          roundCylinderPullback g N.coordinate z v w := by
      rw [radialCylinderTensor_apply]
      convert! h.symm using 1
    rw [← hraw]
    change radialCylinderTensor _ 1 z v w = Q * radialCylinderTensor _ b z v w
    rw [radialCylinderTensor_apply, radialCylinderTensor_apply]
    have hunit' := congrArg (fun r : ℝ => r * v.2 * w.2) hunit
    nlinarith only [hunit']
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hclose
  refine ⟨cylinder_smooth_congr heq hsmooth, bound, hbound, ?_⟩
  intro z hz
  rw [← cylinder_jet_congr heq 0 _ z hz]
  exact hjet z hz

end PoincareConjecture.M35.Uniqueness
