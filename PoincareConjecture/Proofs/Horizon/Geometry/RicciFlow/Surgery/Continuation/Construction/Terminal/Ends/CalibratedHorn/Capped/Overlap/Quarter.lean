import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SphereContact


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem abs_scaled_scalar_sub_one_le_third_on_closure
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ closure N.carrier) :
    |N.scale ^ 2 * D.scalarCurvature x - 1| ≤ 1 / 3 := by
  exact le_on_closure
    (fun y hy => (N.abs_scaled_scalar_sub_one_lt_third_on_carrier D hε hy).le)
    (((continuous_const.mul D.continuous_scalarCurvature).sub continuous_const).abs.continuousOn)
    continuous_const.continuousOn hx

theorem scale_le_three_halves_of_common_closure
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ closure N.carrier) (hxP : x ∈ closure P.carrier) :
    N.scale ≤ (3 / 2 : ℝ) * P.scale := by
  have hn := abs_le.mp (N.abs_scaled_scalar_sub_one_le_third_on_closure N.connection hN hx)
  have hp := abs_le.mp (P.abs_scaled_scalar_sub_one_le_third_on_closure N.connection hP hxP)
  have hsquares : N.scale ^ 2 ≤ 2 * P.scale ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hp.1 (sq_nonneg N.scale)
    have h₂ := mul_le_mul_of_nonneg_left hn.2 (sq_nonneg P.scale)
    nlinarith
  nlinarith [N.scale_pos, P.scale_pos, sq_nonneg (N.scale - (3 / 2 : ℝ) * P.scale)]

theorem edist_le_of_mem_positive_quarter_of_epsilon_le (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 200) {x y : M}
    (hx : x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)
    (hy : y ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
    g.edist x y ≤ ENNReal.ofReal ((0.55 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  let w := N.coordinate_inverse y
  have hz := (N.coordinate_inverse_mem x hx.1).2
  have hw := (N.coordinate_inverse_mem y hy.1).2
  have hxy : g.edist x y ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) +
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * |w.2 - z.2|) := by
    calc
      _ = g.edist (N.coordinate_map (z.1, z.2))
          (N.coordinate_map (w.1, w.2)) := by
        rw [Prod.eta, Prod.eta, N.coordinate_map_coordinate_inverse hx.1,
          N.coordinate_map_coordinate_inverse hy.1]
      _ ≤ g.edist (N.coordinate_map (z.1, z.2)) (N.coordinate_map (w.1, z.2)) +
          g.edist (N.coordinate_map (w.1, z.2)) (N.coordinate_map (w.1, w.2)) :=
        Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add (N.edist_coordinate_map_slice_le z.1 w.1 hz)
        (N.edist_coordinate_map_axis_le w.1 hz hw)
  have haxis : |w.2 - z.2| ≤ N.epsilon⁻¹ / 2 := by
    apply abs_le.mpr
    dsimp [z, w]
    constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
  have hinv : (200 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε (inv_pos.mpr N.epsilon_pos).le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.01 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hsphere : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half, mul_nonneg (Real.sqrt_nonneg (1 + N.epsilon))
      (Real.sqrt_nonneg 2)]
  have hnum : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi +
      Real.sqrt (1 + N.epsilon) * |w.2 - z.2| ≤ (0.55 : ℝ) * N.epsilon⁻¹ := by
    have h₁ := mul_le_mul_of_nonneg_right hsphere Real.pi_pos.le
    have h₂ := mul_le_mul hroot haxis (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1.01)
    nlinarith [Real.pi_le_four]
  have hscale := N.scale_pos
  apply hxy.trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hnum N.scale_pos.le]

theorem edist_le_of_mem_closure_positive_quarter_pair_of_epsilon_le
    (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 200) {x y : M}
    (hx : x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹))
    (hy : y ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    g.edist x y ≤ ENNReal.ofReal ((0.55 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hinterior (z : M) (hz : z ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
      g.edist z y ≤ ENNReal.ofReal ((0.55 : ℝ) * N.scale * N.epsilon⁻¹) :=
    closure_minimal (fun w hw => N.edist_le_of_mem_positive_quarter_of_epsilon_le hε hz hw)
      (isClosed_le (continuous_const.edist continuous_id) continuous_const) hy
  exact closure_minimal hinterior
    (isClosed_le (continuous_id.edist continuous_const) continuous_const) hx

theorem balanced_edist_lower_of_not_mem_carrier_of_epsilon_le (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 200) {x : M} (hx : x ∉ N.carrier) :
    ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤ g.edist N.center x := by
  have hs : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  apply (ENNReal.ofReal_le_ofReal ?_).trans (N.edist_center_lower_of_not_mem_carrier hx)
  nlinarith [mul_le_mul_of_nonneg_right hs
    (mul_nonneg N.scale_pos.le (inv_pos.mpr N.epsilon_pos).le)]

theorem closure_positive_quarter_subset_of_central_sphere_contact_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (heq : P.epsilon = N.epsilon)
    (hcontact : (closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ∩
      P.central_sphere).Nonempty) :
    closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆ P.carrier := by
  obtain ⟨x, hx, hxP⟩ := hcontact
  have hP := heq.trans_le hN
  have hs := N.scale_le_three_halves_of_common_closure P hN hP
    (closure_mono (N.region_subset_carrier _ _) hx)
    (subset_closure (P.central_sphere_subset hxP))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  have hupper : g.edist P.center y ≤
      ENNReal.ofReal ((2 * Real.pi) * P.scale) +
        ENNReal.ofReal ((0.55 : ℝ) * N.scale * N.epsilon⁻¹) := by
    calc
      _ ≤ g.edist P.center x + g.edist x y := Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add
        (P.edist_central_sphere_le_two_pi_mul_scale P.center_on_central_sphere hxP)
        (N.edist_le_of_mem_closure_positive_quarter_pair_of_epsilon_le hN hx hy)
  by_contra hout
  have hlower := P.balanced_edist_lower_of_not_mem_carrier_of_epsilon_le hP hout
  rw [heq] at hlower
  have hinv : (200 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hN (inv_pos.mpr N.epsilon_pos).le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hnum : (2 * Real.pi) * P.scale + (0.55 : ℝ) * N.scale * N.epsilon⁻¹ <
      (0.99 : ℝ) * P.scale * N.epsilon⁻¹ := by
    have h₁ := mul_le_mul_of_nonneg_right hs (inv_pos.mpr N.epsilon_pos).le
    have h₂ := mul_le_mul_of_nonneg_right Real.pi_le_four P.scale_pos.le
    have h₃ := mul_le_mul_of_nonneg_left hinv P.scale_pos.le
    nlinarith [P.scale_pos]
  have hscale := N.scale_pos
  have hscaleP := P.scale_pos
  have hepsilon := N.epsilon_pos
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hupper
  have hlt := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hnum
  exact (not_lt_of_ge (hlower.trans hupper)) hlt

end PoincareConjecture.EpsilonNeck
