import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E}

theorem norm_iteratedFDerivWithin_le_on_compact
    (hS : UniqueDiffOn ℝ S) (f : ℕ → E → F)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) S)
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S) (m : ℕ)
    (hbound : ∃ B : ℝ, ∀ᶠ j in atTop, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ m (f j) S x‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ K →
      ‖iteratedFDerivWithin ℝ m (f j) S x‖ ≤ B := by
  classical
  have hc (j : ℕ) : ContinuousOn (iteratedFDerivWithin ℝ m (f j) S) K :=
    ((hf j).continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) hS).mono hKS
  choose b hb using fun j => hK.exists_bound_of_continuousOn (hc j)
  obtain ⟨B, hB⟩ := hbound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hB
  let C := ∑ j ∈ Finset.range N, max (b j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => le_max_right _ _
  refine ⟨max B 0 + C, add_nonneg (le_max_right _ _) hC, ?_⟩
  intro j x hx
  by_cases hj : N ≤ j
  · exact (hN j hj x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right hC))
  · have hbj : max (b j) 0 ≤ C :=
      Finset.single_le_sum (fun i _ => le_max_right (b i) 0)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hj))
    exact (hb j x hx).trans ((le_max_left _ _).trans
      (hbj.trans (le_add_of_nonneg_left (le_max_right _ _))))

theorem equicontinuous_iteratedFDerivWithin [LocallyCompactSpace S]
    (hconv : Convex ℝ S) (hS : UniqueDiffOn ℝ S) (f : ℕ → E → F)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) S)
    (hbound : ∀ K : Set E, IsCompact K → K ⊆ S → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ j in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f j) S x‖ ≤ B) (m : ℕ) :
    Equicontinuous (fun j (x : S) => iteratedFDerivWithin ℝ m (f j) S x) := by
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hKx
  have hKS : Subtype.val '' K ⊆ S := by rintro _ ⟨z, _, rfl⟩; exact z.property
  obtain ⟨C, hC, hCbound⟩ := norm_iteratedFDerivWithin_le_on_compact hS f hf
    (hK.image continuous_subtype_val) hKS (m + 1)
    (hbound _ (hK.image continuous_subtype_val) hKS (m + 1))
  have hcontained : ball (x : E) r ∩ S ⊆ Subtype.val '' K := by
    intro z hz
    exact ⟨⟨z, hz.2⟩, hball hz.1, rfl⟩
  have hLip (j : ℕ) (y : S) (hy : dist y x < r) :
      ‖iteratedFDerivWithin ℝ m (f j) S (x : E) -
        iteratedFDerivWithin ℝ m (f j) S (y : E)‖ ≤ C * ‖(x : E) - y‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((hf j).differentiableOn_iteratedFDerivWithin
        (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
        hS z hz.2).hasFDerivWithinAt.mono inter_subset_right)
      (fun z hz => ?_) ((convex_ball (x : E) r).inter hconv)
      ⟨hy, y.property⟩ ⟨mem_ball_self hr, x.property⟩
    rw [norm_fderivWithin_iteratedFDerivWithin]
    exact hCbound j z (hcontained hz)
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min r (ε / (C + 1)), lt_min hr (div_pos hε (by linarith)), ?_⟩
  intro y hy j
  have hyr : dist y x < r := hy.trans_le (min_le_left _ _)
  have hys : dist y x < ε / (C + 1) := hy.trans_le (min_le_right _ _)
  calc
    dist (iteratedFDerivWithin ℝ m (f j) S (x : E))
        (iteratedFDerivWithin ℝ m (f j) S (y : E)) ≤ C * dist y x := by
      simpa only [dist_eq_norm, Subtype.dist_eq, norm_sub_rev] using hLip j y hyr
    _ ≤ (C + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hys
