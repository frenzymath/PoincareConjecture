import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceLaterNegativeCut
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierScale
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceBalancedChainAssembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28



theorem exists_later_negative_cut_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N P : EpsilonNeck g), N.epsilon ≤ epsilon₀ → P.epsilon = N.epsilon →
      ∀ {U : Set M}, N.carrier ⊆ U → P.carrier ⊆ U →
      ∀ {γ : ℝ → M} {t₁ tN tP : ℝ}, t₁ < tN → tN < tP →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc t₁ tP) →
        γ tN = N.center → γ tP = P.center →
        (∀ a b, t₁ ≤ a → a ≤ b → b ≤ tP →
          g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b)) →
        g.pathELength γ t₁ tN =
          ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) →
        (N.coordinate_inverse (γ t₁)).2 ≤ -((0.292 : ℝ) * N.epsilon⁻¹) →
        γ t₁ ∈ N.carrier →
        ENNReal.ofReal ((1.9 : ℝ) * N.scale * N.epsilon⁻¹) ≤
          g.pathELength γ tN tP →
        Disjoint P.carrier (N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) := by
  obtain ⟨epsilonS, hSpos, _, hS⟩ :=
    EpsilonNeck.exists_scale_comparison_at_common_closure_m28.{u}
  refine ⟨min epsilonS (1 / 1000), lt_min hSpos (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hsmall heq U hNU hPU γ t₁ tN tP
    h₁ hNP hγ hcN hcP hmin hanchor hsign hz₁ hfar
  have hε : N.epsilon ≤ 1 / 1000 := hsmall.trans (min_le_right _ _)
  have hA : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε (inv_pos.mpr N.epsilon_pos).le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine Set.disjoint_left.mpr fun y hyP hyN => ?_
  have hscale := hS N P (hsmall.trans (min_le_left _ _))
    (by rw [heq]; exact hsmall.trans (min_le_left _ _))
    ⟨y, subset_closure hyN.1, subset_closure hyP⟩
  have hratio : P.scale ≤ (1.1 : ℝ) * N.scale := by
    nlinarith [hscale.2, N.scale_pos]
  have hcut := later_negative_cut_of_minimizer N P hε hA heq hratio hNU hPU
    h₁ hNP hγ hcN hcP hmin (Manifold.pathELength_add h₁.le hNP.le).symm
    hanchor hsign hz₁ hfar
  exact Set.disjoint_left.mp hcut hyP hyN

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem two_source_edges_pathELength_lower
    {N P Q R T : EpsilonNeck g} {γ : ℝ → M} {tN tQ tR tP : ℝ}
    (H₀ : SourceEdgeCommonOrientationPacket N P Q (γ := γ) tN tQ)
    (H₁ : SourceEdgeCommonOrientationPacket Q R T (γ := γ) tQ tR)
    (hNQ : tN < tQ) (hQR : tQ < tR) (hRP : tR ≤ tP)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc tN tP)) :
    ENNReal.ofReal ((1.9 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tN tP := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hfirst : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tN tQ := by
    apply H₀.center_distance.1.trans
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl (hQR.le.trans hRP)))
      H₀.center_N H₀.center_Q hNQ.le
  have hsecond : ENNReal.ofReal ((0.99 : ℝ) * Q.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tQ tR := by
    have hd := H₁.center_distance.1
    rw [H₀.epsilon_eq] at hd
    apply hd.trans
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc hNQ.le hRP)) H₁.center_N H₁.center_Q hQR.le
  have hsum : ENNReal.ofReal
      ((0.99 : ℝ) * N.scale * N.epsilon⁻¹ + (0.99 : ℝ) * Q.scale * N.epsilon⁻¹) ≤
        g.pathELength γ tN tR := by
    rw [ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hA.le)
      (mul_nonneg (mul_nonneg (by norm_num) Q.scale_pos.le) hA.le)]
    exact (add_le_add hfirst hsecond).trans_eq
      (Manifold.pathELength_add hNQ.le hQR.le)
  have hreal : (1.9 : ℝ) * N.scale * N.epsilon⁻¹ ≤
      (0.99 : ℝ) * N.scale * N.epsilon⁻¹ + (0.99 : ℝ) * Q.scale * N.epsilon⁻¹ := by
    have hscale := mul_lt_mul_of_pos_right H₀.scale.1 hA
    nlinarith [mul_pos N.scale_pos hA]
  exact ((ENNReal.ofReal_le_ofReal hreal).trans hsum).trans
    (Manifold.pathELength_mono le_rfl hRP)


theorem SourceEdgePacket.later_negative_cut {N Q : EpsilonNeck g} {epsilon : ℝ}
    (H : SourceEdgePacket N Q epsilon) :
    Disjoint Q.carrier (N.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
  have h := adjacent_later_negative_cut N Q
    (by simpa only [H.epsilon_N] using H.overlap_within_three_quarters)
  simpa only [H.epsilon_N] using h

end PoincareConjecture.M28
