import PoincareConjecture.Proofs.M38.DirectionalRadialAdjustment









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)


def ellipsoidExteriorOpen (t : ℝ) : TopologicalSpace.Opens StandardCapSpace :=
  ⟨{x | t < ‖L.symm x‖}, isOpen_lt continuous_const (continuous_norm.comp L.symm.continuous)⟩


def roundBallExteriorOpen (r : ℝ) : TopologicalSpace.Opens StandardCapSpace :=
  ⟨{x | r < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩


theorem mem_linear_closedBall_image_iff (t : ℝ) (x : StandardCapSpace) :
    x ∈ L '' Metric.closedBall 0 t ↔ ‖L.symm x‖ ≤ t := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [L.symm_apply_apply]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · intro hx
    exact ⟨L.symm x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx,
      L.apply_symm_apply x⟩


theorem ellipsoidExteriorOpen_eq (t : ℝ) :
    (ellipsoidExteriorOpen L t : Set StandardCapSpace) = (L '' Metric.closedBall 0 t)ᶜ := by
  ext x
  change (t < ‖L.symm x‖) ↔ ¬x ∈ L '' Metric.closedBall 0 t
  simp only [mem_linear_closedBall_image_iff, not_le]


theorem roundBallExteriorOpen_eq (r : ℝ) :
    (roundBallExteriorOpen r : Set StandardCapSpace) = (Metric.closedBall 0 r)ᶜ := by
  ext x
  change (r < ‖x‖) ↔ ¬x ∈ Metric.closedBall 0 r
  simp only [Metric.mem_closedBall, dist_zero_right, not_le]


theorem ellipsoid_inverse_norm (x : StandardCapSpace) :
    ‖L.symm x‖ = ‖x‖ * ‖L.symm (capUnitDirection x).val‖ := by
  conv_lhs => rw [← capUnitDirection_radial x]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]


theorem ellipsoid_boundary_radius_le (w : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    t / ‖L.symm w.val‖ ≤ ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * t := by
  have hk : 0 < ‖L.symm w.val‖ :=
    norm_pos_iff.mpr (linearSphereVector_ne_zero L.symm w)
  have hnorm := (L : StandardCapSpace →L[ℝ] StandardCapSpace).le_opNorm (L.symm w.val)
  change ‖L (L.symm w.val)‖ ≤
    ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * ‖L.symm w.val‖ at hnorm
  rw [L.apply_symm_apply, show ‖w.val‖ = 1 by simp] at hnorm
  apply (div_le_iff₀ hk).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnorm ht.le]

variable {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
  (hsize : ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * t ≤ (5 / 4) * ρ)

include ht hρ hsize


theorem ellipsoid_boundary_profile (w : UnitTwoSphere) :
    ρ * ballShrinkProfile (directionalRadialCoefficient L w)
      ((t / ‖L.symm w.val‖) / ρ) = directionalRadialScale L * t := by
  have hk : 0 < ‖L.symm w.val‖ :=
    norm_pos_iff.mpr (linearSphereVector_ne_zero L.symm w)
  have hboundary : t / ‖L.symm w.val‖ ≤ (5 / 4) * ρ :=
    (ellipsoid_boundary_radius_le L w ht).trans hsize
  rw [ballShrinkProfile_linear _ _ ((div_le_iff₀ hρ).mpr hboundary),
    directionalRadialCoefficient]
  field_simp [hρ.ne', hk.ne'] <;> ring


theorem directionalRadialMap_exterior_iff {x : StandardCapSpace} (hx : x ≠ 0) :
    directionalRadialScale L * t < ‖directionalRadialMap L ρ x‖ ↔ t < ‖L.symm x‖ := by
  have hk : 0 < ‖L.symm (capUnitDirection x).val‖ :=
    norm_pos_iff.mpr (linearSphereVector_ne_zero L.symm (capUnitDirection x))
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  rw [← ellipsoid_boundary_profile L ht hρ hsize (capUnitDirection x),
    directionalRadialMap_norm L hρ hx, mul_lt_mul_iff_right₀ hρ,
    (ballShrinkProfile_strictMono hc hc1).lt_iff_lt,
    div_lt_div_iff_of_pos_right hρ, div_lt_iff₀ hk, ellipsoid_inverse_norm L x]

omit hρ hsize in

theorem ellipsoidExterior_ne_zero {x : StandardCapSpace} (hx : t < ‖L.symm x‖) : x ≠ 0 := by
  intro hzero
  have hpos := ht.trans hx
  simpa only [hzero, map_zero, norm_zero, lt_self_iff_false] using hpos


theorem directionalRadialMap_mapsTo_exterior :
    Set.MapsTo (directionalRadialMap L ρ) {x | t < ‖L.symm x‖}
      {y | directionalRadialScale L * t < ‖y‖} := by
  intro x hx
  exact (directionalRadialMap_exterior_iff L ht hρ hsize
    (ellipsoidExterior_ne_zero L ht hx)).mpr hx


theorem directionalRadialInverse_mapsTo_exterior :
    Set.MapsTo (directionalRadialInverse L ρ) {y | directionalRadialScale L * t < ‖y‖}
      {x | t < ‖L.symm x‖} := by
  intro y hy
  have hy0 : y ≠ 0 := norm_pos_iff.mp
    ((mul_pos (directionalRadialScale_pos L) ht).trans hy)
  apply (directionalRadialMap_exterior_iff L ht hρ hsize
    (directionalRadialInverse_ne_zero L hρ hy0)).mp
  rw [directionalRadial_right_inverse L hρ hy0]
  exact hy


theorem directionalRadialMap_exterior_image :
    directionalRadialMap L ρ '' {x | t < ‖L.symm x‖} =
      {y | directionalRadialScale L * t < ‖y‖} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact directionalRadialMap_mapsTo_exterior L ht hρ hsize hx
  · intro y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp
      ((mul_pos (directionalRadialScale_pos L) ht).trans hy)
    exact ⟨directionalRadialInverse L ρ y,
      directionalRadialInverse_mapsTo_exterior L ht hρ hsize hy,
      directionalRadial_right_inverse L hρ hy0⟩


theorem directionalRadialInverse_exterior_image :
    directionalRadialInverse L ρ '' {y | directionalRadialScale L * t < ‖y‖} =
      {x | t < ‖L.symm x‖} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact directionalRadialInverse_mapsTo_exterior L ht hρ hsize hy
  · intro x hx
    exact ⟨directionalRadialMap L ρ x,
      directionalRadialMap_mapsTo_exterior L ht hρ hsize hx,
      directionalRadial_left_inverse L hρ (ellipsoidExterior_ne_zero L ht hx)⟩


noncomputable def ellipsoidComplementDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) (ellipsoidExteriorOpen L t)
      (roundBallExteriorOpen (directionalRadialScale L * t)) ∞ where
  toFun x := ⟨directionalRadialMap L ρ x.val,
    directionalRadialMap_mapsTo_exterior L ht hρ hsize x.property⟩
  invFun y := ⟨directionalRadialInverse L ρ y.val,
    directionalRadialInverse_mapsTo_exterior L ht hρ hsize y.property⟩
  left_inv x := Subtype.ext
    (directionalRadial_left_inverse L hρ (ellipsoidExterior_ne_zero L ht x.property))
  right_inv y := Subtype.ext (directionalRadial_right_inverse L hρ (norm_pos_iff.mp
    ((mul_pos (directionalRadialScale_pos L) ht).trans y.property)))
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (roundBallExteriorOpen (directionalRadialScale L * t)) _).mp
    intro x
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y : ellipsoidExteriorOpen L t => directionalRadialMap L ρ y.val) x
    apply (contMDiffAt_subtype_iff (U := ellipsoidExteriorOpen L t)
      (f := directionalRadialMap L ρ)).mpr
    exact (directionalRadialMap_contDiffAt L
      (ellipsoidExterior_ne_zero L ht x.property)).contMDiffAt
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (ellipsoidExteriorOpen L t) _).mp
    intro y
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun x : roundBallExteriorOpen (directionalRadialScale L * t) =>
        directionalRadialInverse L ρ x.val) y
    apply (contMDiffAt_subtype_iff
      (U := roundBallExteriorOpen (directionalRadialScale L * t))
      (f := directionalRadialInverse L ρ)).mpr
    exact (directionalRadialInverse_contDiffAt L (norm_pos_iff.mp
      ((mul_pos (directionalRadialScale_pos L) ht).trans y.property))).contMDiffAt


theorem ellipsoidComplementDiffeomorph_apply (x : ellipsoidExteriorOpen L t) :
    (ellipsoidComplementDiffeomorph L ht hρ hsize x).val = directionalRadialMap L ρ x.val := rfl


theorem ellipsoidComplementDiffeomorph_symm_apply
    (y : roundBallExteriorOpen (directionalRadialScale L * t)) :
    ((ellipsoidComplementDiffeomorph L ht hρ hsize).symm y).val =
      directionalRadialInverse L ρ y.val := rfl

omit ht hsize in

theorem exists_ellipsoidInnerRadius (R : ℝ) (hR : 0 < R) :
    ∃ s : ℝ, 0 < s ∧ s < R ∧
      ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * s ≤ (5 / 4) * ρ := by
  let K : ℝ := ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖
  let s : ℝ := min (R / 2) (ρ / (2 * (K + 1)))
  have hK : 0 ≤ K := norm_nonneg _
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsR : s < R := (min_le_left _ _).trans_lt (by linarith)
  have hsρ : s ≤ ρ / (2 * (K + 1)) := min_le_right _ _
  have hden : 0 < 2 * (K + 1) := by positivity
  have hbound := (le_div_iff₀ hden).mp hsρ
  refine ⟨s, hs, hsR, ?_⟩
  change K * s ≤ (5 / 4) * ρ
  nlinarith

end PoincareConjecture.M38
