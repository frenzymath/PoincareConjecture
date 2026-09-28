import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityMetric
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}

theorem m65EmbeddingMetric_uniform_bounds (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (compact : IsCompact (univ : Set M)) :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ p (v : EuclideanSpace ℝ (Fin N)),
      c * ‖v‖ ^ 2 ≤ m65EmbeddingMetric g e p v v ∧
        m65EmbeddingMetric g e p v v ≤ C * ‖v‖ ^ 2 := by
  let H := m65EmbeddingMetric g e
  have hH : Continuous H := (m65EmbeddingMetric_contMDiff g e he hinj).continuous
  let S := (univ : Set M) ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1
  have hS : IsCompact S := compact.prod (isCompact_sphere 0 1)
  have hf : ContinuousOn (fun z : M × EuclideanSpace ℝ (Fin N) => H z.1 z.2 z.2) S :=
    (((hH.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd).continuousOn
  have hpos (z : M × EuclideanSpace ℝ (Fin N)) (hz : z ∈ S) : 0 < H z.1 z.2 z.2 := by
    apply m65EmbeddingMetric_pos g e z.1
    have hn := mem_sphere_zero_iff_norm.mp hz.2
    intro heq
    rw [heq, norm_zero] at hn
    norm_num at hn
  obtain ⟨c, hc, hcbound⟩ := hS.exists_forall_le' hf hpos
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hf
  refine ⟨c, max 1 B, hc, le_max_left _ _, ?_⟩
  intro p v
  by_cases hv : v = 0
  · simp [hv]
  let w : EuclideanSpace ℝ (Fin N) := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
  have hrep : ‖v‖ • w = v := by
    simp only [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hwS : (p, w) ∈ S := ⟨mem_univ _, mem_sphere_zero_iff_norm.mpr hw⟩
  have hdiag : H p v v = ‖v‖ ^ 2 * H p w w := by
    calc
      _ = H p (‖v‖ • w) (‖v‖ • w) := by rw [hrep]
      _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
  constructor
  · change c * ‖v‖ ^ 2 ≤ H p v v
    rw [hdiag, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hcbound (p, w) hwS) (sq_nonneg _)
  · change H p v v ≤ max 1 B * ‖v‖ ^ 2
    rw [hdiag, mul_comm (max 1 B)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (le_abs_self (H p w w)).trans ((hB (p, w) hwS).trans (le_max_right _ _))

end PoincareConjecture
