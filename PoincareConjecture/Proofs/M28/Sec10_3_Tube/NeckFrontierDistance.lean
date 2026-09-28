import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckAxialLength
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckExcursionSubarcs

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

open Proofs.M28.NeckLengthComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem coordinate_axial_speed_lower_sharp (N : EpsilonNeck g)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderCoordinates) :
    (N.scale * Real.sqrt (1 - N.epsilon)) * |v.2| ≤
      g.tangentNorm (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) := by
  let P := roundCylinderPullback g N.coordinate_map z v v
  let H := RoundCylinderMetric z v v
  have hfactor : 0 ≤ 1 - N.epsilon := by linarith [N.epsilon_lt_half]
  have hmodel : v.2 ^ 2 ≤ H := by
    dsimp only [H]
    rw [roundCylinderMetric_self_eq]
    nlinarith only [sq_nonneg ‖v.1‖]
  have hH : 0 ≤ H := (sq_nonneg v.2).trans hmodel
  have hbound := mul_le_mul_of_nonneg_left
    (N.normalized_metric_quadratic_bounds z hz v).1 (sq_nonneg N.scale)
  have hcancel : N.scale ^ 2 * (N.scale⁻¹ ^ 2 * P) = P := by
    field_simp [ne_of_gt N.scale_pos]
  change N.scale ^ 2 * ((1 - N.epsilon) * H) ≤
    N.scale ^ 2 * (N.scale⁻¹ ^ 2 * P) at hbound
  rw [hcancel] at hbound
  have hP : 0 ≤ P :=
    (mul_nonneg (sq_nonneg N.scale) (mul_nonneg hfactor hH)).trans hbound
  have haxial := mul_le_mul_of_nonneg_left hmodel
    (mul_nonneg (sq_nonneg N.scale) hfactor)
  change (N.scale * Real.sqrt (1 - N.epsilon)) * |v.2| ≤ Real.sqrt P
  apply (sq_le_sq₀
    (mul_nonneg (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) (abs_nonneg _))
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hfactor, sq_abs, Real.sq_sqrt hP]
  nlinarith only [haxial, hbound]

theorem path_axial_displacement_le_sharp (N : EpsilonNeck g)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγN : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) *
      |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) ≤
        g.pathELength γ a b :=
  M28.path_axial_displacement_le_of_speed N
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
    N.coordinate_axial_speed_lower_sharp hab hγ hγN

theorem edist_central_lower_of_not_mem_region [T2Space M]
    (N : EpsilonNeck g) {r : ℝ} (hr : 0 < r) (hrA : r < N.epsilon⁻¹)
    {p x : M} (hp : p ∈ N.central_sphere) (hx : x ∉ N.region (-r) r) :
    ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) * r) ≤ g.edist p x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra h
  obtain ⟨γ, h0, h1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (lt_of_not_ge h)
  obtain ⟨t, ht0, ht1, hprefix, hheight⟩ :=
    N.exists_first_neck_collar_subarc hr hrA zero_le_one hγ.continuousOn
      (by simpa only [h0] using hp) (by simpa only [h1] using hx)
  have hcost := N.path_axial_displacement_le_sharp ht0.le
    (hγ.mono (Icc_subset_Icc le_rfl ht1)) hprefix
  rw [hheight] at hcost
  exact (not_lt_of_ge (hcost.trans (Manifold.pathELength_mono le_rfl ht1))) hlength

end PoincareConjecture.EpsilonNeck
