import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.QuarterOverlap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem edist_center_lower_of_not_mem_coordinate_slab (N : EpsilonNeck g)
    {r : ℝ} (hr : r ∈ Ioo 0 N.epsilon⁻¹) {x : M}
    (hx : x ∉ N.coordinate_map '' (univ ×ˢ Icc (-r) r)) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) ≤
      g.edist N.center x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra h
  have hdist : Manifold.riemannianEDist (𝓡 3) N.center x <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) := lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdist (show (0 : ℝ) < 1 by norm_num)
  have hcenter := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  have hstart : γ 0 ∈ N.region (-r) r := by
    rw [hγ0]
    exact ⟨hcenter.1, hcenter.2 ▸ neg_lt_zero.mpr hr.1, hcenter.2 ▸ hr.1⟩
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (show (0 : ℝ) ≤ 1 by norm_num) (neg_lt_neg hr.2) hr.2
    hγ.continuous.continuousOn hstart (hγ1 ▸ hx)
  have hax := N.axial_displacement_le_pathELength ht.1.le hγ hcarrier
  have hvalue : |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| = r := by
    rw [hγ0, hcenter.2, sub_zero]
    rcases hboundary with hneg | hpos
    · rw [hneg, abs_neg, abs_of_pos hr.1]
    · rw [hpos, abs_of_pos hr.1]
  rw [hvalue] at hax
  have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  exact (not_lt_of_ge (hax.trans hmono)) hlength

theorem positive_quarter_subset_frontier_neck_inner_slab
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : N'.epsilon = N.epsilon)
    (hscale : (0.99 : ℝ) * N.scale ≤ N'.scale)
    (hcenter : N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      N'.coordinate_map ''
        (univ ×ˢ Icc (-(3 / 4 : ℝ) * N'.epsilon⁻¹) ((3 / 4 : ℝ) * N'.epsilon⁻¹)) := by
  intro x hx
  by_contra hout
  have hinv : 0 < N'.epsilon⁻¹ := inv_pos.mpr N'.epsilon_pos
  have hlower := N'.edist_center_lower_of_not_mem_coordinate_slab
    (r := (3 / 4 : ℝ) * N'.epsilon⁻¹) ⟨by positivity, by linarith⟩ (by
      simpa only [neg_mul] using hout)
  have hupper := N.edist_le_of_mem_closure_positive_quarter hε hx hcenter
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm : g.edist x N'.center = g.edist N'.center x :=
    Manifold.riemannianEDist_comm
  rw [hcomm] at hupper
  rw [heq] at hlower
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hs := N.scale_pos
  have hs' := N'.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hrpos : 0 < Real.sqrt (1 - N.epsilon) := by linarith
  have hprod : (0.99 : ℝ) * ((0.99 : ℝ) * N.scale) ≤
      Real.sqrt (1 - N.epsilon) * N'.scale :=
    mul_le_mul hroot hscale (by positivity) (Real.sqrt_nonneg _)
  have hlt : ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) <
      ENNReal.ofReal (N'.scale * Real.sqrt (1 - N.epsilon) *
        ((3 / 4 : ℝ) * N.epsilon⁻¹)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hprod hi.le, mul_pos hs hi]
  exact (not_lt_of_ge (hlower.trans hupper)) hlt

theorem exists_positive_quarter_subset_frontier_neck_inner_slab_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon = N.epsilon →
      N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
        N'.coordinate_map ''
          (univ ×ˢ Icc (-(3 / 4 : ℝ) * N'.epsilon⁻¹) ((3 / 4 : ℝ) * N'.epsilon⁻¹)) := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := exists_scale_comparison_on_closure.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε heq hcenter
  exact N.positive_quarter_subset_frontier_neck_inner_slab N'
    (hε.trans (min_le_right _ _)) heq
    (hscale N N' (hε.trans (min_le_left _ _))
      (closure_mono (N.region_subset_carrier _ _) hcenter)).1 hcenter

end PoincareConjecture.EpsilonNeck
