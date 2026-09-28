import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityUniformCharts
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeReplacement
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeMetricEnergy
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityCircleEnergy

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture

open M65Interior

theorem m65Embedding_uniform_small_circle_replacement
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M)) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧
      ∀ (U : Set LoopPlane) (F : M65LocalWeakMap e U) (x : LoopPlane) (r : ℝ),
        0 < r → closedBall x r ⊆ U →
        ∀ V W : ℝ → EuclideanSpace ℝ (Fin N),
          AbsolutelyContinuousOnInterval V (-Real.pi) Real.pi →
          V (-Real.pi) = V Real.pi →
          MapsTo V (Icc (-Real.pi) Real.pi) (range e) →
          (V =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
            fun θ => e (F.value (polarPlane x (r, θ)))) →
          MemLp W 2 (volume.restrict (Icc (-Real.pi) Real.pi)) →
          (∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
            V t - V s = ∫ θ in s..t, W θ) →
          (∀ θ ∈ Icc (-Real.pi) Real.pi, ‖V θ - V (-Real.pi)‖ < δ) →
          (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
            (∫ z in closedBall x r, F.derivative i z j * test z +
              e (F.value z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
              r * ∫ θ in (-Real.pi)..Real.pi,
                e (F.value (polarPlane x (r, θ))) j * test (polarPlane x (r, θ)) *
                  Proofs.M58.angularPoint θ i) →
          ∃ G : M65LocalWeakMap e U,
            (∀ z ∉ closedBall x r, G.value z = F.value z ∧
              ∀ i, G.derivative i z = F.derivative i z) ∧
            (∫ z in closedBall x r, m65EmbeddedEnergyDensity g e G.value G.derivative z) ≤
              A * ∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2 := by
  obtain ⟨δ, B, hδ, hB, hcharts⟩ := m65Embedding_uniform_cone_charts e he hinj hemb compact
  obtain ⟨c, C, _, hC, hmetric⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let A := (C * B ^ 2 / 4) * (1 + (2 * Real.pi) ^ 2) * B ^ 2
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨δ, A, hδ, hA, ?_⟩
  intro U F x r hr hDU V W hV hper htarget htrace hW hinc hsmall hgreen
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hstart : -Real.pi ∈ Icc (-Real.pi) Real.pi := ⟨le_rfl, hπ⟩
  obtain ⟨q0, hq0⟩ := htarget hstart
  obtain ⟨p, L, P, ρ, hρ, _, hL, hP, hD, hcapture⟩ := hcharts q0
  let v := fun θ => L (V θ - e p)
  let d := fun θ => L (W θ)
  have hcap (θ : ℝ) (hθ : θ ∈ Icc (-Real.pi) Real.pi) :
      ‖v θ‖ < ρ / 4 ∧ e (P (v θ)) = V θ := by
    obtain ⟨q, hq⟩ := htarget hθ
    have hdist : dist (e q) (e q0) < δ := by
      rw [hq, hq0, dist_eq_norm]
      exact hsmall θ hθ
    have h := hcapture q hdist
    constructor
    · simpa only [v, hq] using h.1
    · simpa only [v, hq] using congrArg e h.2
  obtain ⟨hv, hd, hvi⟩ := linear_circle_data L (e p) hV hW hinc
  have hvc : ContinuousOn v (Icc (-Real.pi) Real.pi) := by
    simpa only [uIcc_of_le hπ] using hv.continuousOn
  have hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ) := by
    intro θ hθ
    rw [mem_closedBall_zero_iff]
    linarith [(hcap θ hθ).1]
  have h0 := hvb hstart
  have hg : ContDiffOn ℝ 1 (e ∘ P) (ball 0 (2 * ρ)) :=
    contMDiffOn_iff_contDiffOn.mp ((he.of_le (by simp)).comp_contMDiffOn hP)
  have htr : (fun θ => P (v θ)) =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun θ => F.value (polarPlane x (r, θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, htrace] with θ hθ ht
    exact hemb.injective ((hcap θ hθ).2.trans ht)
  have hvper : v (-Real.pi) = v Real.pi := by simp only [v, hper]
  obtain ⟨G, hGin, hGout⟩ := F.exists_cone_replacement x hr hρ hB.le hDU P
    hv hvper hg h0 hvb hd hvi hD htr hgreen
  refine ⟨G, hGout, ?_⟩
  have hcone := (coneDisk_metricEnergy_le g e he hinj hemb compact hCpos.le
    (fun q w => (hmetric q w).2) P hr hρ hB.le hvc hg h0 hvb hd hD x).2
  have hcoord := interval_increment_energy_le hπ hvc hd hvi
  have hlinear := clm_circle_energy_le L hW
  have hnorm : ‖L‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg L) hL 2
  have hWnonneg : 0 ≤ ∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ = ∫ z in closedBall x r,
        m65EmbeddedEnergyDensity g e (coneDiskMap P r (v (-Real.pi)) v x)
          (coneDiskField (e ∘ P) r (v (-Real.pi)) v d x) z := by
      apply setIntegral_congr_fun isClosed_closedBall.measurableSet
      intro z hz
      unfold m65EmbeddedEnergyDensity
      simp only [(hGin z hz).1, (hGin z hz).2, v, d]
    _ ≤ (C * B ^ 2 / 4) * ∫ θ in Icc (-Real.pi) Real.pi,
        (‖v θ - v (-Real.pi)‖ ^ 2 + ‖d θ‖ ^ 2) := hcone
    _ ≤ (C * B ^ 2 / 4) *
        ((1 + (2 * Real.pi) ^ 2) * ∫ θ in Icc (-Real.pi) Real.pi, ‖d θ‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [d, sub_neg_eq_add, two_mul] using hcoord
    _ ≤ (C * B ^ 2 / 4) *
        ((1 + (2 * Real.pi) ^ 2) * (‖L‖ ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlinear (by positivity)) (by positivity)
    _ ≤ (C * B ^ 2 / 4) *
        ((1 + (2 * Real.pi) ^ 2) * (B ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm hWnonneg)
          (by positivity)) (by positivity)
    _ = _ := by dsimp only [A]; ring

end PoincareConjecture
