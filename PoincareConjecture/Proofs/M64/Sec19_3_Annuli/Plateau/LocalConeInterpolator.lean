import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorHorizontalColumn












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m64_exists_local_cone_interpolator
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M)) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ H : ℝ × (M × M) → M,
      ContMDiffOn (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
        (Ioo (-1 : ℝ) 2 ×ˢ {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}) ∧
      (∀ p q, g.edist p q ≤ ENNReal.ofReal (r / 2) →
        H (0, p, q) = p ∧ H (1, p, q) = q ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (H (t, p, q))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
              (g.edist p q).toReal) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : TangentSpace (𝓡 n) q,
          g.tangentNorm (H (t, p, q))
            (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
              (t, p, q) (0, 0, w)) ≤ B * g.tangentNorm q w)) ∧
      (∀ p t, H (t, p, p) = p) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, hr, H, hH, hgeom, hdiag, _⟩ :=
    M63.exists_smooth_minimizing_interpolator g hcompact
  obtain ⟨B, hB, hbound⟩ :=
    m64_interpolator_endpoint_bound_on_short_tube g hcompact hr H hH 1
  refine ⟨r, hr, B, hB, H, hH, ?_, hdiag⟩
  intro p q hpq
  have hshort : g.edist p q < ENNReal.ofReal r :=
    hpq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  obtain ⟨h0, h1, _, hspeed, _⟩ := hgeom p q hshort
  refine ⟨h0, h1, ?_, ?_⟩
  · intro t ht
    exact hspeed t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht w
    let L := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H (t, p, q)
    change ‖L (0, 0, w)‖ ≤ B * ‖w‖
    by_cases hw : w = 0
    · subst w
      change ‖L 0‖ ≤ B * ‖(0 : TangentSpace (𝓡 n) q)‖
      simp
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hunit : g.tangentNorm q (‖w‖⁻¹ • w) ≤ 1 := by
      change ‖‖w‖⁻¹ • w‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hwpos.ne']
    have hb := hbound t ht p q hpq 0 (by change ‖(0 : TangentSpace (𝓡 n) p)‖ ≤ 1; simp)
      (‖w‖⁻¹ • w) hunit
    have hin : ((0 : ℝ), (0 : TangentSpace (𝓡 n) p), ‖w‖⁻¹ • w) =
        ‖w‖⁻¹ • ((0 : ℝ), (0 : TangentSpace (𝓡 n) p), w) := by simp
    change ‖L (0, 0, ‖w‖⁻¹ • w)‖ ≤ B at hb
    rw [hin, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm] at hb
    have hm := mul_le_mul_of_nonneg_left hb hwpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hwpos.ne', one_mul] at hm
    simpa only [mul_comm] using hm

end PoincareConjecture
