import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.ProfileBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
# The positive bilinear form of the initial cap

Morgan-Tian Lemma 12.2, printed pp. 294-295, constructs the metric of a
rotational hypersurface. Here its arclength expression is a literal
continuous bilinear form on each copy of Euclidean three-space. This
file proves positivity, symmetry and orthogonal invariance; smoothness
of the field, its connection and curvature are separate obligations.
See `proof-work/tasks/M34/derivations/radial-profile.md`.
-/

set_option autoImplicit false

open scoped ContDiff Topology

namespace PoincareMT.M34

/-- The angular eigenvalue of the cap metric in Cartesian coordinates
(Lemma 12.2, pp. 294-295). Its value at zero is the round-tip limit. -/
noncomputable def capAngularCoefficient (a r : ℝ) : ℝ :=
  if r = 0 then 1 else (capProfile a r / r) ^ 2

/-- The coefficient of the radial rank-one correction. The value at
zero is the radius-two sphere's limit, from Lemma 12.2, p. 294. -/
noncomputable def capRadialCoefficient (a r : ℝ) : ℝ :=
  if r = 0 then 1 / 12 else (1 - capAngularCoefficient a r) / r ^ 2

/-- The angular coefficient is positive at every geometric radius,
so the metric has no degenerate angular directions (Lemma 12.2, p. 295). -/
theorem capAngularCoefficient_pos {a r : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) : 0 < capAngularCoefficient a r := by
  by_cases h : r = 0
  · simp only [capAngularCoefficient, h, if_true]
    norm_num
  · rw [capAngularCoefficient, if_neg h]
    exact sq_pos_of_pos (div_pos (capProfile_pos ha hapi (lt_of_le_of_ne hr (Ne.symm h)))
      (lt_of_le_of_ne hr (Ne.symm h)))

/-- The angular coefficient is at most one because the profile's radial
speed is at most one (Lemma 12.2, pp. 294-295). -/
theorem capAngularCoefficient_le_one {a r : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) : capAngularCoefficient a r ≤ 1 := by
  by_cases h : r = 0
  · simp only [capAngularCoefficient, h, if_true, le_refl]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm h)
    have hpos : 0 ≤ capProfile a r / r := (div_pos (capProfile_pos ha hapi hrp) hrp).le
    have hle : capProfile a r / r ≤ 1 :=
      (div_le_one hrp).mpr (capProfile_le_radius a hr)
    rw [capAngularCoefficient, if_neg h]
    nlinarith

/-- The radial correction is nonnegative (Lemma 12.2, pp. 294-295). -/
theorem capRadialCoefficient_nonneg {a r : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) : 0 ≤ capRadialCoefficient a r := by
  by_cases h : r = 0
  · simp only [capRadialCoefficient, h, if_true]
    norm_num
  · rw [capRadialCoefficient, if_neg h]
    exact div_nonneg (sub_nonneg.mpr (capAngularCoefficient_le_one ha hapi hr))
      (sq_nonneg r)

/-- Cartesian expression of `dr^2 + f(r)^2 g_unit_S2`, including the tip
(Lemma 12.2, pp. 294-295). -/
noncomputable def capMetricInner (a : ℝ) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := innerSL ℝ
  capAngularCoefficient a ‖x‖ • B +
    capRadialCoefficient a ‖x‖ • (B x).smulRight (B x)

/-- Evaluation of the cap's actual continuous bilinear form
(Lemma 12.2, pp. 294-295). -/
theorem capMetricInner_apply (a : ℝ) (x u v : StandardCapSpace) :
    capMetricInner a x u v = capAngularCoefficient a ‖x‖ * inner ℝ u v +
      capRadialCoefficient a ‖x‖ * (inner ℝ x u * inner ℝ x v) := rfl

/-- At the origin the metric agrees with the Euclidean inner product
(Lemma 12.2, p. 294). -/
theorem capMetricInner_zero (a : ℝ) (u v : StandardCapSpace) :
    capMetricInner a 0 u v = inner ℝ u v := by
  simp only [capMetricInner_apply, norm_zero, capAngularCoefficient, if_true,
    inner_zero_left, mul_zero, one_mul, add_zero]

/-- Symmetry of the cap's bilinear form (Lemma 12.2, pp. 294-295). -/
theorem capMetricInner_symm (a : ℝ) (x u v : StandardCapSpace) :
    capMetricInner a x u v = capMetricInner a x v u := by
  rw [capMetricInner_apply, capMetricInner_apply, real_inner_comm u v,
    mul_comm (inner ℝ x u) (inner ℝ x v)]

/-- Positive definiteness is proved before the form is packaged as a
Riemannian metric (Lemma 12.2, pp. 294-295). -/
theorem capMetricInner_pos {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi / 2)
    (x v : StandardCapSpace) (hv : v ≠ 0) : 0 < capMetricInner a x v v := by
  rw [capMetricInner_apply]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (capAngularCoefficient_pos ha hapi (norm_nonneg x))
      (real_inner_self_pos.mpr hv))
    (mul_nonneg (capRadialCoefficient_nonneg ha hapi (norm_nonneg x))
      (mul_self_nonneg _))

/-- The radial vector keeps its Euclidean length. This is the algebraic
input for the arclength distance identity (Lemma 12.2, pp. 294-295). -/
theorem capMetricInner_radial (a : ℝ) (x : StandardCapSpace) :
    capMetricInner a x x x = ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp only [hx, capMetricInner_zero, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [capMetricInner_apply, real_inner_self_eq_norm_sq, capRadialCoefficient, if_neg hn]
    field_simp
    ring

/-- Orthogonal linear maps preserve the actual bilinear form. The literal
SO(3) action is a specialization (Definition 12.1 and Lemma 12.2, pp. 293-295). -/
theorem capMetricInner_linearIsometry (a : ℝ)
    (A : StandardCapSpace →ₗᵢ[ℝ] StandardCapSpace) (x u v : StandardCapSpace) :
    capMetricInner a (A x) (A u) (A v) = capMetricInner a x u v := by
  simp only [capMetricInner_apply, A.norm_map, A.inner_map_map]

end PoincareMT.M34
