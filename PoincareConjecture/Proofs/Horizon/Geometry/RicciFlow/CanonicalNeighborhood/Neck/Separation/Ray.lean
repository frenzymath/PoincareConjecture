import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Ray
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Depth.Points
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false

open Set
open scoped Manifold ContDiff
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

theorem half_neck_depth_gt_central_slab_bound (N : EpsilonNeck g)
    (hN : N.epsilon ≤ 1 / (4 * neckDepthConstant * (2 * Real.pi + 2)))
    {x : M} (hx : x ∈ N.carrier) {σ : ℝ} (hσ : |σ| = 1)
    (haxis : (N.coordinate_inverse x).2 = σ / (2 * N.epsilon))
    {y : M} (hy : y ∈ N.central_sphere) :
    (2 * Real.pi + 2) * N.scale < (g.edist x y).toReal := by
  have hC : 0 < neckDepthConstant := neckDepthConstant_pos
  have hε := N.epsilon_pos
  have hr := N.scale_pos
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hεbound := (le_div_iff₀ (show 0 <
    4 * neckDepthConstant * (2 * Real.pi + 2) by positivity)).mp hN
  have hnum : neckDepthConstant * N.epsilon * (2 * Real.pi + 2) ≤ 1 / 4 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hnum hr.le
  have hroot_scaled := mul_le_mul_of_nonneg_left hroot hr.le
  have hstrict : (2 * Real.pi + 2) * N.scale <
      N.scale * Real.sqrt (1 - N.epsilon) / (neckDepthConstant * N.epsilon) := by
    apply (lt_div_iff₀ (mul_pos hC hε)).mpr
    nlinarith
  exact hstrict.trans_le (N.half_neck_depth_lower_bound hx hσ haxis hy)

theorem minimizing_half_neck_not_mem_compact_side (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hN : N.epsilon ≤ 1 / (4 * neckDepthConstant * (2 * Real.pi + 2)))
    {A : Set M} (hA : IsOpen A) (hfront : frontier A = N.central_sphere)
    {γ : ℝ → M} {L : ℝ} (hγ : IsMinimizingOn γ (Icc 0 L))
    (hout : γ L ∉ A) (hstart : γ 0 ∈ N.carrier)
    (haxis0 : |(N.coordinate_inverse (γ 0)).2| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 L) (hmem : γ t ∈ N.carrier)
    {σ : ℝ} (hσ : |σ| = 1)
    (haxis : (N.coordinate_inverse (γ t)).2 = σ / (2 * N.epsilon)) : γ t ∉ A := by
  intro hinside
  have hbound : ∀ y ∈ frontier A, dist (γ 0) y ≤ (2 * Real.pi + 2) * N.scale := by
    intro y hy
    rw [hdist]
    exact N.toReal_edist_central_sphere_le_of_abs_axis_le_one hstart (hfront ▸ hy) haxis0
  obtain ⟨y, hy, hdy⟩ := hγ.exists_frontier_distance_le_of_mem hA hout hbound ht hinside
  rw [hfront] at hy
  have hdeep := N.half_neck_depth_gt_central_slab_bound hN hmem hσ haxis hy
  rw [← hdist] at hdeep
  linarith [ht.1]

theorem minimizing_half_neck_outward_sign (N : EpsilonNeck g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hN : N.epsilon ≤ 1 / (4 * neckDepthConstant * (2 * Real.pi + 2)))
    {A B : Set M} (hA : IsOpen A) (hfront : frontier A = N.central_sphere)
    (hhalf :
      (N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
      (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A))
    {γ : ℝ → M} {L : ℝ} (hγ : IsMinimizingOn γ (Icc 0 L))
    (hout : γ L ∉ A) (hstart : γ 0 ∈ N.carrier)
    (haxis0 : |(N.coordinate_inverse (γ 0)).2| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 L) (hmem : γ t ∈ N.carrier)
    {σ : ℝ} (hσ : |σ| = 1)
    (haxis : (N.coordinate_inverse (γ t)).2 = σ / (2 * N.epsilon)) :
    (N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B ∧ σ = 1) ∨
    (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A ∧ σ = -1) := by
  have houtside := N.minimizing_half_neck_not_mem_compact_side hdist hN hA hfront
    hγ hout hstart haxis0 ht hmem hσ haxis
  have hε := N.epsilon_pos
  have hpos : 0 < 1 / (2 * N.epsilon) := by positivity
  have hsign : σ = 1 ∨ σ = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hσ
  have hcoord := (N.coordinate_inverse_mem _ hmem).2
  rcases hhalf with ⟨hneg, hposhalf⟩ | ⟨hneg, hposhalf⟩
  · refine Or.inl ⟨hneg, hposhalf, ?_⟩
    rcases hsign with hsign | hsign
    · exact hsign
    · exfalso
      apply houtside (hneg ⟨hmem, hcoord.1, ?_⟩)
      rw [haxis, hsign]
      exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · refine Or.inr ⟨hneg, hposhalf, ?_⟩
    rcases hsign with hsign | hsign
    · exfalso
      apply houtside (hposhalf ⟨hmem, ?_, hcoord.2⟩)
      simpa only [haxis, hsign] using hpos
    · exact hsign

end PoincareConjecture.EpsilonNeck
