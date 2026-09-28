import PoincareConjecture.Proofs.M35.CapGeometry.RadialAnnulusPatch
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

noncomputable def intrinsicRadialAnnulusPatch (q₀ : UnitTwoSphere) (a b length : ℝ)
    (hb : 0 < b) (hl : 0 < length) (hinner : 0 < a - b * length) :
    StandardCylinderPatch length
      (intrinsicSpatialInverse g hrotation hcomplete (a • q₀.val)) := by
  let F := intrinsicSpatialDiffeomorph g hrotation hcomplete
  let N := radialAnnulusPatch q₀ a b length hb hl hinner
  refine {
    length_pos := hl
    carrier := F ⁻¹' N.carrier
    carrier_open := N.carrier_open.preimage F.continuous
    coordinate := F.symm ∘ N.coordinate
    inverse := N.inverse ∘ F
    coordinate_image := ?_
    coordinate_left_inverse := ?_
    coordinate_right_inverse := ?_
    inverse_domain := fun x hx => N.inverse_domain (F x) hx
    coordinate_smooth := F.symm.contMDiff.comp_contMDiffOn N.coordinate_smooth
    inverse_smooth := N.inverse_smooth.comp F.contMDiff.contMDiffOn (fun _ hx => hx)
    center_sphere := ?_
  }
  · rw [image_comp, N.coordinate_image, F.symm_image_eq_preimage]
  · intro z hz
    change N.inverse (F (F.symm (N.coordinate z))) = z
    rw [F.apply_symm_apply]
    exact N.coordinate_left_inverse hz
  · intro x hx
    change F.symm (N.coordinate (N.inverse (F x))) = x
    rw [N.coordinate_right_inverse hx, F.symm_apply_apply]
  · obtain ⟨q, hq⟩ := N.center_sphere
    exact ⟨q, congrArg F.symm hq⟩

theorem intrinsicRadialAnnulusPatch_carrier (q₀ : UnitTwoSphere) (a b length : ℝ)
    (hb : 0 < b) (hl : 0 < length) (hinner : 0 < a - b * length) :
    (intrinsicRadialAnnulusPatch g hrotation hcomplete q₀ a b length hb hl hinner).carrier =
      {x | a - b * length < radialArclength g ‖x‖ ∧
        radialArclength g ‖x‖ < a + b * length} := by
  ext x
  change (a - b * length < ‖intrinsicSpatialCoordinate g x‖ ∧
    ‖intrinsicSpatialCoordinate g x‖ < a + b * length) ↔ _
  rw [intrinsicSpatialCoordinate_norm]
  rfl

theorem intrinsicRadialAnnulusPatch_centralSphere (q₀ : UnitTwoSphere)
    (a b length : ℝ) (hb : 0 < b) (hl : 0 < length)
    (hinner : 0 < a - b * length) :
    (intrinsicRadialAnnulusPatch g hrotation hcomplete q₀ a b length
      hb hl hinner).centralSphere =
        sphere 0 ((radialArclengthOrderIso g hrotation hcomplete).symm a) := by
  let F := intrinsicSpatialDiffeomorph g hrotation hcomplete
  let N := radialAnnulusPatch q₀ a b length hb hl hinner
  change (F.symm ∘ N.coordinate) '' (univ ×ˢ ({0} : Set ℝ)) = _
  rw [image_comp]
  change F.symm '' N.centralSphere = _
  rw [radialAnnulusPatch_centralSphere, F.symm_image_eq_preimage]
  ext x
  simp only [mem_preimage, mem_sphere, dist_zero_right]
  change ‖intrinsicSpatialCoordinate g x‖ = a ↔
    ‖x‖ = (radialArclengthOrderIso g hrotation hcomplete).symm a
  rw [intrinsicSpatialCoordinate_norm]
  let R := radialArclengthOrderIso g hrotation hcomplete
  change R ‖x‖ = a ↔ ‖x‖ = R.symm a
  constructor
  · intro hx
    exact (R.symm_apply_apply ‖x‖).symm.trans (congrArg R.symm hx)
  · intro hx
    rw [hx, R.apply_symm_apply]

theorem intrinsicRadialAnnulusPatch_closed_core_eq (P : M35StandardCapPredecessors)
    (q₀ : UnitTwoSphere) (a b length : ℝ) (hb : 0 < b) (hl : 0 < length)
    (hinner : 0 < a - b * length) :
    closure (g.ball 0 (a - b * length)) = g.ball 0 (a + b * length) \
      (intrinsicRadialAnnulusPatch g hrotation hcomplete q₀ a b length
        hb hl hinner).carrier := by
  rw [closure_ball_zero_eq_radial_closedBall g hrotation hcomplete P hinner,
    intrinsicRadialAnnulusPatch_carrier]
  ext x
  rw [mem_closedBall, dist_zero_right, mem_sdiff, RiemannianMetric.ball,
    mem_ofPred_eq, edist_zero_eq_radialArclength g hrotation hcomplete P]
  have hs : 0 ≤ radialArclength g ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg x)
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs]
  let R := radialArclengthOrderIso g hrotation hcomplete
  have hle : ‖x‖ ≤ R.symm (a - b * length) ↔ R ‖x‖ ≤ a - b * length := by
    constructor
    · intro h
      simpa only [R.apply_symm_apply] using R.monotone h
    · intro h
      simpa only [R.symm_apply_apply] using R.symm.monotone h
  rw [hle]
  have hwidth : 0 < b * length := mul_pos hb hl
  constructor
  · intro h
    refine ⟨by change R ‖x‖ < _; linarith, ?_⟩
    exact fun hc => not_lt_of_ge h hc.1
  · rintro ⟨h, hc⟩
    exact le_of_not_gt (fun hi => hc ⟨hi, h⟩)

end PoincareConjecture.M35.Uniqueness
