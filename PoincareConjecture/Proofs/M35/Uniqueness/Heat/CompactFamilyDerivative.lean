import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CoefficientDerivative
import Mathlib.Topology.ContinuousMap.Compact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {X E : Type*} [MetricSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivWithinAt_compact_family {a b : ℝ}
    (f d : ℝ → C(X, E))
    (hdf : ∀ t ∈ Icc a b, ∀ x : X,
      HasDerivWithinAt (fun s => f s x) (d t x) (Icc a b) t)
    (hdc : ContinuousOn (fun p : ℝ × X => d p.1 p.2) (Icc a b ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt f (d t) (Icc a b) t := by
  have huc := (isCompact_Icc.prod isCompact_univ).uniformContinuousOn_of_continuous hdc
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ)] with s hs hst
  let U := Icc a b ∩ Metric.ball t δ
  have htU : t ∈ U := ⟨ht, Metric.mem_ball_self hδ⟩
  have hsU : s ∈ U := ⟨hs, hst⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hb (r : ℝ) (hr : r ∈ U) : ‖d r x - d t x‖ ≤ ε := by
    have hdist : dist (r, x) (t, x) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
        (Metric.mem_ball.mp hr.2)
    simpa only [dist_eq_norm] using
      (hclose (r, x) ⟨hr.1, mem_univ x⟩ (t, x) ⟨ht, mem_univ x⟩ hdist).le
  have hd (r : ℝ) (hr : r ∈ U) :
      HasDerivWithinAt (fun q => f q x - q • d t x) (d r x - d t x) U r := by
    have hl : HasDerivWithinAt (fun q : ℝ => q • d t x) (d t x) U r := by
      simpa only [id_eq, one_smul] using! ((hasDerivAt_id r).smul_const (d t x)).hasDerivWithinAt
    exact ((hdf r hr.1 x).mono inter_subset_left).sub hl
  have hU : Convex ℝ U := (convex_Icc a b).inter (convex_ball t δ)
  have hm := hU.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb htU hsU
  have he : (f s x - s • d t x) - (f t x - t • d t x) =
      f s x - f t x - (s - t) • d t x := by rw [sub_smul]; abel
  rw [he] at hm
  simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply] using hm

theorem contDiffOn_compact_family_of_jets {a b : ℝ} (hab : a < b)
    (f : ℕ → ℝ → C(X, E))
    (hdf : ∀ k t, t ∈ Icc a b → ∀ x : X,
      HasDerivWithinAt (fun s => f k s x) (f (k + 1) t x) (Icc a b) t)
    (hc : ∀ k, ContinuousOn (fun p : ℝ × X => f k p.1 p.2) (Icc a b ×ˢ univ)) :
    ContDiffOn ℝ ∞ (f 0) (Icc a b) := by
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (f k) (f (k + 1) t) (Icc a b) t :=
    hasDerivWithinAt_compact_family (f k) (f (k + 1)) (hdf k) (hc (k + 1)) ht
  have hfinite (r : ℕ) : ∀ k, ContDiffOn ℝ r (f k) (Icc a b) := by
    induction r with
    | zero =>
      intro k
      exact contDiffOn_zero.mpr (fun t ht => (hd k t ht).continuousWithinAt)
    | succ r ih =>
      intro k
      rw [show (↑(r + 1) : ℕ∞ω) = (r : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
      refine ⟨fun t ht => (hd k t ht).differentiableWithinAt, ?_, ?_⟩
      · simp
      · exact (ih (k + 1)).congr (fun t ht =>
          (hd k t ht).derivWithin ((uniqueDiffOn_Icc hab) t ht))
  exact contDiffOn_infty.mpr (fun r => hfinite r 0)

end PoincareConjecture.M35.Uniqueness.Heat
