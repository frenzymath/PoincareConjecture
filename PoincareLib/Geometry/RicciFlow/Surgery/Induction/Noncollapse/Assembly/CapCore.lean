import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.RegularRegion
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.LocalVolume

/-!
# The actual core radius in the canonical cap case

Morgan--Tian Definition 9.72(7), pp. 230-231, and Proposition 16.3,
p. 368. The cap's scalar supremum and supplied core volume retain their
literal radius. The scalar-ratio bound compares this radius with the
tested radius; no equality of the two radii is asserted.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.Proofs.M46

variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

/-- An actual core point lies in the certified cap carrier. -/
theorem canonicalCap_core_mem_carrier {x : M} (hx : x ∈ N.core) : x ∈ N.carrier := by
  rw [N.core_eq_interior_closed_core] at hx
  have h := interior_subset hx
  rw [N.closed_core_eq_complement_end] at h
  exact h.1

/-- The scalar supremum has a nonempty bounded range on the actual core
ball, so both directions of its pointwise comparison are legitimate. -/
theorem canonicalCap_core_scalar_bounds {x : M} (hx : x ∈ N.core)
    {B : ℝ} (hB : N.cap_constant ≤ B) :
    (∀ y ∈ g.ball x (N.core_radius x),
      N.connection.scalarCurvature y ≤ (N.core_radius x)⁻¹ ^ 2) ∧
    (N.core_radius x)⁻¹ ^ 2 ≤ B * N.connection.scalarCurvature x := by
  have hq := N.core_radius_pos x hx
  have hxcarrier := canonicalCap_core_mem_carrier N hx
  have hxball : x ∈ g.ball x (N.core_radius x) := by
    simpa [RiemannianMetric.ball, RiemannianMetric.edist,
      Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hq
  obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
  let f : {y : M // y ∈ g.ball x (N.core_radius x)} → ℝ :=
    fun y => N.connection.scalarCurvature y.val
  have hf (y : {y : M // y ∈ g.ball x (N.core_radius x)}) :
      f y ≤ B * N.connection.scalarCurvature x := by
    apply (hratio x hxcarrier y (N.core_ball_subset x hx (subset_closure y.property))).trans
    exact mul_le_mul_of_nonneg_right (hb.le.trans hB) (N.scalar_pos x hxcarrier).le
  have hbounded : BddAbove (range f) := ⟨B * N.connection.scalarCurvature x, by
    rintro _ ⟨y, rfl⟩
    exact hf y⟩
  have hnonempty : (range f).Nonempty := ⟨f ⟨x, hxball⟩, mem_range_self _⟩
  constructor
  · intro y hy
    rw [← N.core_radius_eq x hx]
    exact le_csSup hbounded (mem_range.mpr ⟨⟨y, hy⟩, rfl⟩)
  · rw [← N.core_radius_eq x hx]
    exact csSup_le hnonempty (by rintro _ ⟨y, rfl⟩; exact hf y)

/-- The supplied core volume retains a constant depending only on the
upper bound B for the cap constant. -/
theorem canonicalCap_core_volume {x : M} (hx : x ∈ N.core)
    {B : ℝ} (hB : N.cap_constant ≤ B) :
    ENNReal.ofReal (B⁻¹ * N.core_radius x ^ 3) ≤
      calibratedMetricVolume g (g.ball x (N.core_radius x)) := by
  have hBpos := N.cap_constant_pos.trans_le hB
  obtain ⟨b, hb, hvolume⟩ := N.core_ball_volume_lower
  apply le_trans _ (hvolume x hx)
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (((inv_le_inv₀ hBpos N.cap_constant_pos).mpr hB).trans hb.le)
    (pow_nonneg (N.core_radius_pos x hx).le _)

/-- High center scalar forces the actual core radius below the chosen
surgery radius. This is the scale needed by the pinching estimate. -/
theorem canonicalCap_core_radius_le {x : M} (hx : x ∈ N.core)
    {r : ℝ} (hr : 0 < r)
    (hhigh : r⁻¹ ^ 2 ≤ N.connection.scalarCurvature x) : N.core_radius x ≤ r := by
  have hq := N.core_radius_pos x hx
  have hxball : x ∈ g.ball x (N.core_radius x) := by
    simpa [RiemannianMetric.ball, RiemannianMetric.edist,
      Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hq
  have hscalar := (canonicalCap_core_scalar_bounds N hx (le_refl N.cap_constant)).1 x hxball
  have hi := (sq_le_sq₀ (inv_pos.mpr hr).le (inv_pos.mpr hq).le).mp (hhigh.trans hscalar)
  exact (inv_le_inv₀ hr hq).mp hi

/-- The tested full-curvature trace compares its radius with the cap
core radius, with one fixed loss depending only on B. -/
theorem canonicalCap_test_radius_le {x : M} (hx : x ∈ N.core)
    {B s : ℝ} (hB1 : 1 ≤ B) (hB : N.cap_constant ≤ B) (hs : 0 < s)
    (hscalar : N.connection.scalarCurvature x ≤ 9 * s⁻¹ ^ 2) :
    s ≤ 3 * B * N.core_radius x := by
  have hq := N.core_radius_pos x hx
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hsup := (canonicalCap_core_scalar_bounds N hx hB).2.trans
    (mul_le_mul_of_nonneg_left hscalar hBpos.le)
  have hscaled := mul_le_mul_of_nonneg_right hsup (sq_nonneg (s * N.core_radius x))
  field_simp [hs.ne', hq.ne'] at hscaled
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right hBsq (by positivity : 0 ≤ 9 * N.core_radius x ^ 2)
  have hnonneg : 0 ≤ 3 * B * N.core_radius x := by positivity
  nlinarith

end PoincareMT.Proofs.M46
