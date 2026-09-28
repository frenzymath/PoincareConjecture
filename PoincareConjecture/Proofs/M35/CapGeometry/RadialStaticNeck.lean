import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialAnnulusMetric
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCylinderTensor
import PoincareConjecture.Proofs.M35.CapGeometry.RadialPointIdentification
import PoincareConjecture.Proofs.M35.CapGeometry.RadialDerivativeBall
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

theorem intrinsic_radial_center_norm (hcomplete : MetricComplete g)
    (q : UnitTwoSphere) (x : StandardCapSpace) :
    ‖intrinsicSpatialInverse g hrotation hcomplete (radialArclength g ‖x‖ • q.val)‖ =
      ‖x‖ := by
  have ha : 0 ≤ radialArclength g ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg x)
  rw [intrinsicSpatialInverse_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
    norm_eq_of_mem_sphere, mul_one]
  exact (radialArclengthOrderIso g hrotation hcomplete).symm_apply_apply ‖x‖

theorem scalar_intrinsic_radial_center (P : M35StandardCapPredecessors)
    (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q) (hcomplete : MetricComplete g)
    (q : UnitTwoSphere) (x : StandardCapSpace) :
    let G := M13.scaleSmoothMetric g Q hQ
    let hrot := scaleSmoothMetric_rotation_invariant hrotation Q hQ
    let hc := scaleSmoothMetric_complete g hcomplete Q hQ
    D.scalarCurvature (intrinsicSpatialInverse G hrot hc
      (radialArclength G ‖x‖ • q.val)) = D.scalarCurvature x := by
  dsimp only
  rw [(rotational_scalar_edist_eq_axis P D hrotation _).1,
    intrinsic_radial_center_norm, ← (rotational_scalar_edist_eq_axis P D hrotation x).1]

noncomputable def radialStaticNeck
    (atlas : StandardCylinderAtlas) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (hcomplete : MetricComplete g)
    (q : UnitTwoSphere) (a b epsilon : ℝ) (hb : 0 < b)
    (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1 / 2)
    (hinner : 0 < a - b * epsilon⁻¹)
    (hscalar :
      let G := M13.scaleSmoothMetric g Q hQ
      let hrot := scaleSmoothMetric_rotation_invariant hrotation Q hQ
      let hc := scaleSmoothMetric_complete g hcomplete Q hQ
      D.scalarCurvature (intrinsicSpatialInverse G hrot hc (a • q.val)) = Q)
    (hclose :
      let G := M13.scaleSmoothMetric g Q hQ
      let hrot := scaleSmoothMetric_rotation_invariant hrotation Q hQ
      let hc := scaleSmoothMetric_complete g hcomplete Q hQ
      RoundCylinderClose epsilon 0 (radialCylinderTensor
        (fun u => intrinsicWarpingRadius G hrot hc (a + b * u) ^ 2) b)) :
    StandardStaticNeck atlas g D epsilon := by
  let G := M13.scaleSmoothMetric g Q hQ
  have hrot := scaleSmoothMetric_rotation_invariant hrotation Q hQ
  have hc := scaleSmoothMetric_complete g hcomplete Q hQ
  let N := intrinsicRadialAnnulusPatch G hrot hc q a b epsilon⁻¹ hb
    (inv_pos.mpr hepsilon) hinner
  refine {
    epsilon_pos := hepsilon
    epsilon_lt_half := hepsilon'
    center := intrinsicSpatialInverse G hrot hc (a • q.val)
    scalar_pos := by rw [hscalar]; exact hQ
    patch := N
    close := ?_
  }
  change RoundCylinderClose epsilon 0 (fun z v w =>
    D.scalarCurvature (intrinsicSpatialInverse G hrot hc (a • q.val)) *
      roundCylinderPullback g N.coordinate z v w)
  rw [hscalar]
  let B := radialCylinderTensor
    (fun u => intrinsicWarpingRadius G hrot hc (a + b * u) ^ 2) b
  have heq : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = Q * roundCylinderPullback g N.coordinate z v w := by
    intro z hz v w
    change radialCylinderTensor _ b z v w = _
    rw [radialCylinderTensor_apply]
    have h := intrinsicRadialAnnulusPatch_pullback G hrot hc q a b epsilon⁻¹ hb
      (inv_pos.mpr hepsilon) hinner z hz v w
    calc
      _ = roundCylinderPullback G N.coordinate z v w := by
        convert! h.symm using 1
      _ = _ := M13.scaleSmoothMetric_inner g Q hQ _ _ _
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hclose
  refine ⟨cylinder_smooth_congr heq hsmooth, bound, hbound, ?_⟩
  intro z hz
  rw [← cylinder_jet_congr heq 0 _ z hz]
  exact hjet z hz

end PoincareConjecture.M35.Uniqueness
