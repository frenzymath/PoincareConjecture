import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.Belt



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

def capCollarClock (r : Real) : Real := (1 - r ^ 2) / (2 * r)

@[simp] theorem capCollarClock_one : capCollarClock 1 = 0 := by
  norm_num [capCollarClock]

theorem capCollarClock_antitone {r R : Real} (hr : 0 < r) (hrR : r ≤ R) :
    capCollarClock R ≤ capCollarClock r := by
  have hR : 0 < R := hr.trans_le hrR
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * R) (by positivity : 0 < 2 * r)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (show 0 ≤ 1 + r * R by positivity)]

theorem capCollarClock_bounds {R : Real} (hR : 1 ≤ R) (hR' : R ≤ 5 / 4) :
    -(1 / 4) ≤ capCollarClock R ∧ capCollarClock R ≤ 0 := by
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * R)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hR') (show 0 ≤ 5 / 4 + R by linarith)]
  · simpa using capCollarClock_antitone (by norm_num : (0 : Real) < 1) hR

theorem exists_capCollarClock_preimage {R t : Real} (hR : 1 ≤ R)
    (ht : t ∈ Icc (capCollarClock R) 0) :
    ∃ r ∈ Icc 1 R, capCollarClock r = t := by
  have hc : ContinuousOn capCollarClock (Icc 1 R) := by
    intro r hr
    exact ((continuousAt_const.sub (continuousAt_id.pow 2)).div
      (continuousAt_const.mul continuousAt_id) (by
        change 2 * r ≠ 0
        nlinarith [hr.1])).continuousWithinAt
  exact intermediate_value_Icc' hR hc (by simpa using ht)



theorem image_extended_cap_eq_truncated_model
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (γ : S1 → Hemisphere.Plane v)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (g : E2 → E3)
    (hcore : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)}))
    {η R : Real} (hR : 1 < R) (hR' : R ≤ 5 / 4) (hRη : R - 1 < η)
    (hcollar : ∀ p : S1, ∀ r : Real, |r - 1| < η →
      g (r • (p : E2)) = (c + s * capCollarClock r) • v + (γ p : E3)) :
    g '' closedBall (0 : E2) R =
      liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | capCollarClock R ≤
            inner Real v (boundedCylinderRadius v p • (p : E3))}) := by
  let T := liftPlaneDiffeomorph hv c s hs A
  let graph : S2 → E3 := fun p => boundedCylinderRadius v p • (p : E3)
  have hclock := capCollarClock_bounds hR.le hR'
  have hcollar' (p : S1) (r : Real) (hr : r ∈ Icc 1 R) :
      g (r • (p : E2)) = (c + s * capCollarClock r) • v + (γ p : E3) :=
    hcollar p r (by rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]; linarith [hr.2])
  have hheight (t : Real) (q : Hemisphere.Plane v) :
      inner Real v (t • v + (q : E3)) = t := by
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.property]
  have hproj (t : Real) (q : Hemisphere.Plane v) :
      (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (q : E3)) = q := by
    simp [Hemisphere.Plane]
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_cases hx1 : ‖x‖ ≤ 1
    · have hmem := hcore ▸ mem_image_of_mem g (mem_closedBall_zero_iff.mpr hx1)
      obtain ⟨z, ⟨p, hp, rfl⟩, heq⟩ := hmem
      refine ⟨graph p, ⟨p, ?_, rfl⟩, heq⟩
      change capCollarClock R ≤ inner Real v (boundedCylinderRadius v p • (p : E3))
      rw [inner_smul_right]
      exact hclock.2.trans (mul_nonneg (boundedCylinderRadius_pos v p).le hp)
    · have hxpos : 0 < ‖x‖ := by linarith
      let p : S1 := ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hxpos), inv_mul_cancel₀ hxpos.ne']⟩
      have hxp : ‖x‖ • (p : E2) = x := by
        change ‖x‖ • (‖x‖⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
      have hxr : ‖x‖ ∈ Icc 1 R := ⟨le_of_not_ge hx1, mem_closedBall_zero_iff.mp hx⟩
      obtain ⟨q, hq, hqp⟩ := hboundary.symm ▸ mem_range_self p
      let z : E3 := capCollarClock ‖x‖ • v + (q : E3)
      have hzt : inner Real v z = capCollarClock ‖x‖ := hheight _ q
      have hzlo : capCollarClock R ≤ inner Real v z := by
        rw [hzt]
        exact capCollarClock_antitone hxpos hxr.2
      have hzhi : inner Real v z ≤ 0 := by
        rw [hzt]
        simpa using capCollarClock_antitone (by norm_num : (0 : Real) < 1) hxr.1
      have hzgraph : z ∈ range graph :=
        (mem_boundedCylinder_sphere_iff_of_height_belt v hv z
          (abs_le.mpr ⟨hclock.1.trans hzlo, hzhi.trans (by norm_num)⟩)).mpr (by
            rw [hproj]; exact mem_sphere_zero_iff_norm.mp hq)
      obtain ⟨u, hu⟩ := hzgraph
      refine ⟨z, ⟨u, ?_, hu⟩, ?_⟩
      · change capCollarClock R ≤ inner Real v (graph u)
        rw [hu]
        exact hzlo
      rw [← hxp, hcollar' p ‖x‖ hxr]
      rw [liftPlaneDiffeomorph_apply, hzt, hproj, hqp]
  · rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    by_cases hp0 : 0 ≤ inner Real v (graph p)
    · apply image_mono (closedBall_subset_closedBall hR.le)
      rw [hcore]
      refine ⟨graph p, ⟨p, ?_, rfl⟩, rfl⟩
      change 0 ≤ inner Real v (p : E3)
      have hh : 0 ≤ boundedCylinderRadius v p * inner Real v (p : E3) := by
        simpa only [graph, inner_smul_right] using hp0
      nlinarith [boundedCylinderRadius_pos v p]
    · have ht : inner Real v (graph p) ∈ Icc (capCollarClock R) 0 :=
        ⟨hp, (lt_of_not_ge hp0).le⟩
      obtain ⟨r, hr, hrt⟩ := exists_capCollarClock_preimage hR.le ht
      let q := (Hemisphere.Plane v).orthogonalProjectionOnto (graph p)
      have hq : q ∈ sphere (0 : Hemisphere.Plane v) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact norm_boundedCylinder_projection_eq_one_of_height_belt v hv p
          (abs_le.mpr ⟨hclock.1.trans ht.1, ht.2.trans (by norm_num)⟩)
      obtain ⟨u, hu⟩ := hboundary ▸ mem_image_of_mem A hq
      refine ⟨r • (u : E2), ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show 0 < r by linarith [hr.1]), norm_eq_of_mem_sphere, mul_one]
        exact hr.2
      · rw [hcollar' u r hr, hrt, hu]
        rfl

end Poincare.Manifold.Schoenflies.Reverse
