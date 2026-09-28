import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SphereContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.CollarDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_closure_positive_quarter_subset_closedCollar_of_central_sphere_contact :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        (closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ∩ P.central_sphere).Nonempty →
          closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆
            P.closedCollar ((0.75 : ℝ) * P.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := exists_scale_comparison_at_common_closure.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq ⟨x, hx, hxP⟩ y hy
  have hsmall : N.epsilon ≤ 1 / 1000 := hε.trans (min_le_right _ _)
  have hN : N.epsilon ≤ ε₁ := hε.trans (min_le_left _ _)
  have hs := (hscale N P hN (heq ▸ hN)
    ⟨x, closure_mono (N.region_subset_carrier _ _) hx,
      subset_closure (P.central_sphere_subset hxP)⟩).1
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hupper : g.edist P.center y ≤
      ENNReal.ofReal ((2 * Real.pi) * P.scale) +
        ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
    calc
      _ ≤ g.edist P.center x + g.edist x y := Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add
        (P.edist_central_sphere_le_two_pi_mul_scale P.center_on_central_sphere hxP)
        (N.edist_le_of_mem_closure_positive_quarter_pair hsmall hx hy)
  by_contra hout
  have hPε : 0 < P.epsilon⁻¹ := inv_pos.mpr P.epsilon_pos
  have hlower := P.edist_center_lower_of_not_mem_closedCollar
    (show 0 < (0.75 : ℝ) * P.epsilon⁻¹ by positivity)
    (show (0.75 : ℝ) * P.epsilon⁻¹ < P.epsilon⁻¹ by linarith) hout
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - P.epsilon) := by
    have hPsmall : P.epsilon ≤ 1 / 1000 := heq ▸ hsmall
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - P.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - P.epsilon)]
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  have hscaleN := N.scale_pos
  have hscaleP := P.scale_pos
  have hinvpos := inv_pos.mpr N.epsilon_pos
  have hnum : (2 * Real.pi) * P.scale + (0.51 : ℝ) * N.scale * N.epsilon⁻¹ <
      P.scale * Real.sqrt (1 - P.epsilon) * ((0.75 : ℝ) * P.epsilon⁻¹) := by
    rw [heq]
    rw [heq] at hroot
    have h1 := mul_le_mul_of_nonneg_right hs hinvpos.le
    have h2 := mul_le_mul_of_nonneg_right Real.pi_le_four hscaleP.le
    have h3 := mul_le_mul_of_nonneg_left hinv hscaleP.le
    have h4 := mul_le_mul_of_nonneg_right hroot (mul_nonneg hscaleP.le hinvpos.le)
    nlinarith [mul_pos hscaleP hinvpos]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hupper
  have hlt := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hnum
  exact (not_lt_of_ge (hlower.trans hupper)) hlt

end PoincareConjecture.EpsilonNeck
