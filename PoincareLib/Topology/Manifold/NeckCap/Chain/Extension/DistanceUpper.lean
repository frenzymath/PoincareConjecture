import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

/-!
# The upper balanced distance at a neck frontier

Retaining the exact axial distortion in the metric comparison gives the
`1.01` upper bound required when extending a balanced chain by a neck whose
center lies on the frontier. No completeness of the ambient metric is needed.

Reference: Morgan--Tian, Lemma A.17 and equation (A.1), pp. 506--507.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- The distance to an interior point retains its actual axial height. -/
theorem edist_center_le_height_bound {x : M} (hx : x ∈ N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal
      ((2 * Real.pi + Real.sqrt (1 + N.epsilon) *
        |(N.coordinate_inverse x).2|) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  have hscale := N.scale_pos
  have hepsilon := N.epsilon_pos
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord : N.coordinate_map z = x := by
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    rwa [N.coordinate_map_eq] at h
  have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have haxial := N.edist_coordinate_map_axis_le z.1 hzero hz
  simp only [sub_zero] at haxial
  rw [Prod.eta z, hcoord] at haxial
  calc
    g.edist N.center x ≤ g.edist N.center (N.coordinate_map (z.1, 0)) +
        g.edist (N.coordinate_map (z.1, 0)) x := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((2 * Real.pi) * N.scale) +
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * |z.2|) :=
      add_le_add (N.edist_central_sphere_le_two_pi_mul_scale
        N.center_on_central_sphere hcentral) haxial
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The axial contribution retains its exact upper metric-comparison factor. -/
theorem edist_center_le_model_bound_of_mem_carrier {x : M} (hx : x ∈ N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal
      ((2 * Real.pi + Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹) * N.scale) := by
  apply (N.edist_center_le_height_bound hx).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ N.scale_pos.le
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hz := (N.coordinate_inverse_mem x hx).2
  exact abs_le.mpr ⟨hz.1.le, hz.2.le⟩

/-- Closed metric balls retain the carrier bound at any ambient frontier point. -/
theorem edist_center_le_model_bound_of_mem_closure {x : M} (hx : x ∈ closure N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal
      ((2 * Real.pi + Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact closure_minimal (fun y hy => N.edist_center_le_model_bound_of_mem_carrier hy)
    (isClosed_le (continuous_const.edist continuous_id) continuous_const) hx

/-- The published balanced upper distance holds uniformly on the closure
when the neck parameter is at most `1/1000`. -/
theorem edist_center_le_balanced_upper_of_mem_closure
    (hε : N.epsilon ≤ 1 / 1000) {x : M} (hx : x ∈ closure N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal ((1.01 : ℝ) * N.scale * N.epsilon⁻¹) := by
  apply (N.edist_center_le_model_bound_of_mem_closure hx).trans
  apply ENNReal.ofReal_le_ofReal
  have hinv_pos := inv_pos.mpr N.epsilon_pos
  have hsmall := mul_le_mul_of_nonneg_right hε hinv_pos.le
  rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at hsmall
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hbound : 2 * Real.pi + Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ ≤
      (1.01 : ℝ) * N.epsilon⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hroot hinv_pos.le
    nlinarith [Real.pi_le_four]
  calc
    _ ≤ ((1.01 : ℝ) * N.epsilon⁻¹) * N.scale :=
      mul_le_mul_of_nonneg_right hbound N.scale_pos.le
    _ = _ := by ring

end PoincareMT.EpsilonNeck
