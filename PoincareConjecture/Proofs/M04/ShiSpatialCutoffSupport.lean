import PoincareConjecture.Proofs.M04.ShiNativeDistanceSupport
import PoincareConjecture.Proofs.M04.ShiCappedDistance
import PoincareConjecture.Proofs.M04.ShiCutoffProfile









set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 800000 in
theorem exists_shi_spatial_cutoff_lower_support [T2Space M]
    (D : LeviCivitaData g) (p q : M) {R K b C₁ C₂ G ε : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K) (hb : 0 < b) (hcap : 1 ≤ b * R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hRm : ∀ y ∈ g.ball p R, D.curvatureTensorNorm y ≤ K)
    (hC₁ : 0 < C₁) (hC₂ : 0 ≤ C₂) (hG : 0 ≤ G)
    (hprofile : ∀ s : ℝ, -C₁ ≤ deriv shiCutoffProfile s ∧
      deriv shiCutoffProfile s ≤ 0 ∧
      |deriv (deriv shiCutoffProfile) s| ≤ C₂ ∧
      (deriv shiCutoffProfile s) ^ 2 ≤ G * shiCutoffProfile s)
    (hpos : 0 < shiCutoffProfile (b * shiCappedDistance g p R q))
    (hε : 0 < ε) :
    ∃ (V : Set M) (v : M → ℝ), IsOpen V ∧ q ∈ V ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ v V ∧
      v q = shiCutoffProfile (b * shiCappedDistance g p R q) ∧
      (∀ᶠ y in 𝓝 q, v y ≤ shiCutoffProfile (b * shiCappedDistance g p R y)) ∧
      scalarGradientSq g v q ≤
        G * b ^ 2 * shiCutoffProfile (b * shiCappedDistance g p R q) ∧
      -D.laplacian v q ≤
        (2 * (n : ℝ) * C₁ + C₂) * b ^ 2 + C₁ * (n : ℝ) * K + ε := by
  have hlt : b * shiCappedDistance g p R q < 1 := by
    by_contra hn
    have hz := shiCutoffProfile_zero (le_of_not_gt hn)
    exact (ne_of_gt hpos) hz
  have hqball : q ∈ g.ball p R := by
    by_contra hq
    have he := shiCappedDistance_eq_of_le_edist hR.le (le_of_not_gt hq)
    rw [he] at hlt
    exact (not_lt_of_ge hcap) hlt
  have hdist := shiCappedDistance_eq_of_mem_ball hqball
  by_cases hhalf : b * shiCappedDistance g p R q < 1 / 2
  · have heq : shiCutoffProfile (b * shiCappedDistance g p R q) = 1 :=
      shiCutoffProfile_one hhalf.le
    have hcont : Continuous (fun y => b * shiCappedDistance g p R y) :=
      continuous_const.mul (continuous_shiCappedDistance g p R)
    have hgerm : ∀ᶠ y in 𝓝 q, b * shiCappedDistance g p R y < 1 / 2 :=
      hcont.continuousAt.eventually (gt_mem_nhds hhalf)
    refine ⟨univ, fun _ => 1, isOpen_univ, mem_univ q, contMDiffOn_const,
      heq.symm, ?_, ?_, ?_⟩
    · filter_upwards [hgerm] with y hy
      rw [shiCutoffProfile_one hy.le]
    · have hz : scalarGradientSq g (fun _ : M => (1 : ℝ)) q = 0 := by
        simp [scalarGradientSq, mvfderiv_const]
      rw [hz]
      exact mul_nonneg (mul_nonneg hG (sq_nonneg b)) hpos.le
    · have hz : D.laplacian (fun _ : M => (1 : ℝ)) q = 0 := by
        simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
          LeviCivitaData.hessianOnFields, mvfderiv_const]
      rw [hz, neg_zero]
      positivity
  · have hhalf' : 1 / 2 ≤ b * (g.edist p q).toReal := by
      simpa only [hdist] using le_of_not_gt hhalf
    have hd : 0 < (g.edist p q).toReal := by
      apply (mul_pos_iff_of_pos_left hb).mp
      linarith only [hhalf']
    have hδ : 0 < ε / (C₁ * b) := div_pos hε (mul_pos hC₁ hb)
    obtain ⟨U, u, hU, hqU, hu, huq, hupper, hgrad, hlap⟩ :=
      exists_shi_native_distance_upper_support D p q R K hcompact hqball hd hK
        hRm (ε / (C₁ * b)) hδ
    have huqpos : 0 < u q := huq.symm ▸ hd
    have hucont : ContinuousAt u q := hu.continuousOn.continuousAt (hU.mem_nhds hqU)
    have hugerm : ∀ᶠ y in 𝓝 q, 0 < u y := hucont.eventually (lt_mem_nhds huqpos)
    have hφ : ContDiff ℝ ∞ (fun s : ℝ => shiCutoffProfile (b * s)) :=
      shiCutoffProfile_smooth.comp (contDiff_const.mul contDiff_id)
    have huv : u q = shiCappedDistance g p R q := huq.trans hdist.symm
    have hκ : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK
    have hcomp := shiCutoffProfile_composition_bounds D hU hu hqU hb hκ hδ.le
      hC₁.le hC₂ hG (hprofile (b * u q)) huqpos
      (by simpa only [huq] using hhalf')
      (by simpa only [huv] using hlt.le) hgrad
      (by simpa only [huq] using hlap)
    refine ⟨U, fun y => shiCutoffProfile (b * u y), hU, hqU,
      hφ.contMDiff.comp_contMDiffOn hu, ?_, ?_, ?_, ?_⟩
    · exact congrArg (fun s : ℝ => shiCutoffProfile (b * s)) huv
    · filter_upwards [hU.mem_nhds hqU, hugerm] with y hyU hypos
      have hle : shiCappedDistance g p R y ≤ u y :=
        ENNReal.toReal_le_of_le_ofReal hypos.le
          ((min_le_left _ _).trans (hupper y hyU))
      exact shiCutoffProfile_antitone (mul_le_mul_of_nonneg_left hle hb.le)
    · simpa only [huv] using hcomp.1
    · have herr : C₁ * b * (ε / (C₁ * b)) = ε := by
        field_simp [ne_of_gt hC₁, ne_of_gt hb]
      simpa only [herr, mul_assoc] using hcomp.2

end PoincareConjecture.M04

