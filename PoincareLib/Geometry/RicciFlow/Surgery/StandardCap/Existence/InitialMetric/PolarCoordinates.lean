import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Completeness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.SphereRegularity
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Polar coordinates on the cap's cylindrical end

Morgan-Tian Definition 12.1 and Lemma 12.2, printed pp. 293-295.
The end map is a radial translation of ordinary polar coordinates.
Its inverse is smooth away from zero and includes the end boundary.
See `proof-work/tasks/M34/derivations/cylindrical-end.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

/-- A fixed unit vector supplies the otherwise unused total inverse
value at the origin (Lemma 12.2 polar inverse, pp. 294-295). -/
noncomputable def capNorthPole : UnitTwoSphere :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- Radial direction, defined on all of the cap but used only away from
zero in the end inverse (Definition 12.1, pp. 293-294). -/
noncomputable def capDirection (x : StandardCapSpace) : UnitTwoSphere := by
  classical
  exact if hx : x = 0 then capNorthPole else
    ⟨‖x‖⁻¹ • x, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

/-- The chosen total extension agrees with normalization away from
zero (Definition 12.1 end coordinates, pp. 293-294). -/
theorem capDirection_coe {x : StandardCapSpace} (hx : x ≠ 0) :
    (capDirection x : StandardCapSpace) = ‖x‖⁻¹ • x := by
  simp only [capDirection, dif_neg hx]

/-- Normalization recovers every positive ray's unit direction
(Lemma 12.2, pp. 294-295). -/
theorem capDirection_smul {r : ℝ} (hr : 0 < r) (u : UnitTwoSphere) :
    capDirection (r • (u : StandardCapSpace)) = u := by
  have hn : ‖r • (u : StandardCapSpace)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere u, mul_one]
  have hx : r • (u : StandardCapSpace) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hn]; exact hr.ne')
  apply Subtype.ext
  rw [capDirection_coe hx, hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The literal cylinder-to-cap coordinate map with end radius `R`
(Definition 12.1 and Lemma 12.2, pp. 293-295). -/
noncomputable def capCylinderCoordinate (R : ℝ) (z : StandardCylinderSpace) :
    StandardCapSpace := (R + z.2) • (z.1 : StandardCapSpace)

/-- A total inverse whose geometric domain has strictly positive radius
(Definition 12.1 and Lemma 12.2, pp. 293-295). -/
noncomputable def capCylinderInverse (R : ℝ) (x : StandardCapSpace) :
    StandardCylinderSpace := (capDirection x, ‖x‖ - R)

/-- The coordinate radius is `R+z` on the positive polar domain
(Definition 12.1, pp. 293-294). -/
theorem capCylinderCoordinate_norm (R : ℝ) (z : StandardCylinderSpace)
    (hz : 0 < R + z.2) : ‖capCylinderCoordinate R z‖ = R + z.2 := by
  rw [capCylinderCoordinate, norm_smul, Real.norm_eq_abs, abs_of_pos hz,
    norm_eq_of_mem_sphere z.1, mul_one]

/-- The inverse is a left inverse on every positive coordinate radius
(Definition 12.1, pp. 293-294). -/
theorem capCylinderInverse_coordinate (R : ℝ) (z : StandardCylinderSpace)
    (hz : 0 < R + z.2) : capCylinderInverse R (capCylinderCoordinate R z) = z := by
  apply Prod.ext
  · exact capDirection_smul hz z.1
  · change ‖capCylinderCoordinate R z‖ - R = z.2
    rw [capCylinderCoordinate_norm R z hz]
    ring

/-- The coordinate is a right inverse at every nonzero cap point
(Definition 12.1, pp. 293-294). -/
theorem capCylinderCoordinate_inverse (R : ℝ) {x : StandardCapSpace} (hx : x ≠ 0) :
    capCylinderCoordinate R (capCylinderInverse R x) = x := by
  change (R + (‖x‖ - R)) • (capDirection x : StandardCapSpace) = x
  rw [capDirection_coe hx, show R + (‖x‖ - R) = ‖x‖ by ring,
    smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- The half-cylinder maps exactly onto the exterior including its
boundary sphere (Definition 12.1, pp. 293-294). -/
theorem capCylinderCoordinate_image {R : ℝ} (hR : 0 < R) :
    capCylinderCoordinate R '' (univ ×ˢ Ici (0 : ℝ)) =
      {x : StandardCapSpace | R ≤ ‖x‖} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change R ≤ ‖capCylinderCoordinate R z‖
    rw [capCylinderCoordinate_norm R z (by have := hz.2; change 0 ≤ z.2 at this; linarith)]
    exact le_add_of_nonneg_right hz.2
  · intro hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
    refine ⟨capCylinderInverse R x, ⟨mem_univ _, ?_⟩, capCylinderCoordinate_inverse R hx0⟩
    change 0 ≤ ‖x‖ - R
    exact sub_nonneg.mpr hx

/-- The polar coordinate map is globally smooth; the end uses only its
positive-radius collar (Definition 12.1, pp. 293-294). -/
theorem capCylinderCoordinate_contMDiff (R : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (capCylinderCoordinate R) := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  exact (contMDiff_const.add contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

/-- The normalization into the sphere is smooth at nonzero points,
with no assertion about the arbitrary value at zero (Lemma 12.2, p. 295). -/
theorem capDirection_contMDiffAt {x : StandardCapSpace} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 2) ∞ capDirection x := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  apply ContMDiffAt.of_coe_sphere
  rw [contMDiffAt_iff_contDiffAt]
  apply (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
    contDiffAt_id).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact capDirection_coe hy

/-- The actual cylinder-valued inverse is smooth at every nonzero
point, hence on the whole closed end carrier (Definition 12.1, pp. 293-294). -/
theorem capCylinderInverse_contMDiffAt (R : ℝ) {x : StandardCapSpace} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (capCylinderInverse R) x := by
  exact (capDirection_contMDiffAt hx).prodMk
    (((contDiffAt_norm ℝ hx).sub contDiffAt_const).contMDiffAt)

end PoincareMT.M34
