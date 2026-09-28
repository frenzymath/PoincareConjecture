import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LowerOrderDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set Filter
open scoped Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ} {ι E : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem hasDerivWithinAt_coefficientOperator
    (L : (ι → 𝓢(X, ℝ)) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ f : ι → 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ i x, ‖f i x‖ ≤ M) → ‖L f‖ ≤ C * M)
    {a b : ℝ} {S : Set X} (hS : IsCompact S)
    (f d : ℝ → ι → 𝓢(X, ℝ))
    (hdf : ∀ t ∈ Icc a b, ∀ i x,
      HasDerivWithinAt (fun s => f s i x) (d t i x) (Icc a b) t)
    (hdc : ContinuousOn (fun p : ℝ × X => fun i => d p.1 i p.2) (Icc a b ×ˢ S))
    (hfS : ∀ t ∈ Icc a b, ∀ i x, x ∉ S → f t i x = 0)
    (hdS : ∀ t ∈ Icc a b, ∀ i x, x ∉ S → d t i x = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => L (f s)) (L (d t)) (Icc a b) t := by
  let : Fintype ι := Fintype.ofFinite ι
  have huc := (isCompact_Icc.prod hS).uniformContinuousOn_of_continuous hdc
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hdiv : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc _ hdiv
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ)] with s hs hst
  let U := Icc a b ∩ Metric.ball t δ
  have htU : t ∈ U := ⟨ht, Metric.mem_ball_self hδ⟩
  have hsU : s ∈ U := ⟨hs, hst⟩
  have hb (i : ι) (x : X) :
      ‖f s i x - f t i x - (s - t) * d t i x‖ ≤ (ε / (C + 1)) * ‖s - t‖ := by
    by_cases hx : x ∈ S
    · have hbound (r : ℝ) (hr : r ∈ U) : ‖d r i x - d t i x‖ ≤ ε / (C + 1) := by
        have hdist : dist (r, x) (t, x) < δ := by
          simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
            (Metric.mem_ball.mp hr.2)
        have hnorm := hclose (r, x) ⟨hr.1, hx⟩ (t, x) ⟨ht, hx⟩ hdist
        exact (norm_le_pi_norm (fun j => d r j x - d t j x) i).trans
          (by simpa only [dist_eq_norm, Pi.sub_def] using hnorm.le)
      have hd (r : ℝ) (hr : r ∈ U) :
          HasDerivWithinAt (fun q => f q i x - q * d t i x)
            (d r i x - d t i x) U r := by
        have hl : HasDerivWithinAt (fun q : ℝ => q * d t i x) (d t i x) U r := by
          simpa only [id_eq, one_mul] using!
            ((hasDerivAt_id r).mul_const (d t i x)).hasDerivWithinAt
        exact ((hdf r hr.1 i x).mono inter_subset_left).sub hl
      have hU : Convex ℝ U := (convex_Icc a b).inter (convex_ball t δ)
      have hm := hU.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound htU hsU
      have he : (f s i x - s * d t i x) - (f t i x - t * d t i x) =
          f s i x - f t i x - (s - t) * d t i x := by ring
      rwa [he] at hm
    · simp only [hfS s hs i x hx, hfS t ht i x hx, hdS t ht i x hx,
        mul_zero, sub_zero, norm_zero]
      positivity
  have hnorm : ‖L (f s - f t - (s - t) • d t)‖ ≤
      C * ((ε / (C + 1)) * ‖s - t‖) :=
    hL _ _ (mul_nonneg hdiv.le (norm_nonneg _)) (by
      intro i x
      simpa only [Pi.sub_apply, Pi.smul_apply, sub_apply, smul_apply, smul_eq_mul] using hb i x)
  rw [map_sub, map_sub, map_smul] at hnorm
  apply hnorm.trans
  have hεC : C * (ε / (C + 1)) ≤ ε := by
    calc
      C * (ε / (C + 1)) ≤ (C + 1) * (ε / (C + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) hdiv.le
      _ = ε := mul_div_cancel₀ ε (by linarith)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hεC (norm_nonneg (s - t))

end PoincareConjecture.M35.Uniqueness.Heat
