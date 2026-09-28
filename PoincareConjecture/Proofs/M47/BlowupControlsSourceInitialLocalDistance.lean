import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_MetricBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ChartTopology
import PoincareConjecture.Proofs.M34.Standard.PathLengthComparison
import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem source_initial_comparison_tip_distance_lt
    {g0 : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta r : ℝ}
    (Q : SurgeryCapClose g0 S g tip scale eta)
    (heta : eta ≤ 1) (hrEta : r ≤ eta⁻¹)
    {x : StandardCapSpace} (hx : x ∈ g0.metric.ball 0 r) :
    g.edist tip (Q.map x) < ENNReal.ofReal (2 * scale * r) := by
  have hsource : g0.metric.ball 0 r ⊆ g0.metric.ball 0 eta⁻¹ := by
    intro z hz
    exact hz.trans_le (ENNReal.ofReal_le_ofReal hrEta)
  have hnorm (z : StandardCapSpace) (hz : z ∈ g0.metric.ball 0 eta⁻¹)
      (v : TangentSpace (𝓡 3) z) :
      g.tangentNorm (Q.map z) (mfderiv (𝓡 3) (𝓡 3) Q.map z v) ≤
        (2 * scale) * g0.metric.tangentNorm z v := by
    have h := (Q.quadratic_bounds hz v).2
    have hg0 : 0 ≤ g0.metric.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g0.metric.pos z v hv).le
    have hscale : scale ^ 2 * scale⁻¹ ^ 2 = 1 := by field_simp [Q.scale_pos.ne']
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg scale)
    rw [← mul_assoc, hscale, one_mul] at hmul
    change Real.sqrt _ ≤ (2 * scale) * Real.sqrt _
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) (Real.sqrt_nonneg _), ?_⟩
    rw [mul_pow, Real.sq_sqrt hg0]
    have hsmall := mul_le_mul_of_nonneg_right heta (mul_nonneg (sq_nonneg scale) hg0)
    nlinarith only [hmul, hsmall, mul_nonneg (sq_nonneg scale) hg0]
  obtain ⟨p, hp0, hp1, hp, hlength, hball⟩ := g0.metric.exists_short_path_in_ball 0 x hx
  have hmap : MapsTo p (Icc (0 : ℝ) 1) (g0.metric.ball 0 eta⁻¹) :=
    fun s hs => hsource (hball hs)
  have hQp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (Q.map ∘ p) (Icc (0 : ℝ) 1) :=
    (Q.map_smooth.of_le (by simp)).comp hp hmap
  have hspeed (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      g.tangentNorm ((Q.map ∘ p) s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (Q.map ∘ p) s 1) ≤
        (2 * scale) * g0.metric.tangentNorm (p s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) p s 1) := by
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have hf := (Q.map_smooth.contMDiffAt
      (Q.toPartialDiffeomorph.open_source.mem_nhds (hmap hs'))).mdifferentiableAt (by simp)
    have hp' := ((hp s hs').contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
      (by simp)
    rw [mfderiv_comp_apply s hf hp']
    exact hnorm (p s) (hmap hs') _
  have hlen := g.pathELength_le_mul_of_speed_le g0.metric (Q.map ∘ p) p 0 1
    (mul_nonneg (by norm_num) Q.scale_pos.le) hspeed
  have hd := M36.metric_edist_le_pathELength g zero_le_one hQp
  simp only [Function.comp_apply, hp0, hp1, Q.map_tip] at hd
  have hstrict : ENNReal.ofReal (2 * scale) * g0.metric.pathELength p 0 1 <
      ENNReal.ofReal (2 * scale) * ENNReal.ofReal r := by
    exact ENNReal.mul_lt_mul_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Q.scale_pos)))
      ENNReal.ofReal_ne_top hlength
  exact (hd.trans hlen).trans_lt (hstrict.trans_eq
    (ENNReal.ofReal_mul (mul_nonneg (by norm_num) Q.scale_pos.le)).symm)

end PoincareConjecture.M47
