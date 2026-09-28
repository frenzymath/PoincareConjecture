import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLinearChart











set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}





theorem m65Embedding_exists_bounded_chart (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (p : M) :
    ∃ (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (P : EuclideanSpace ℝ (Fin 3) → M) (ρ δ K : ℝ),
      0 < ρ ∧ 0 < δ ∧ 0 < K ∧ P 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) 1 P (ball 0 (2 * ρ)) ∧
      (∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
        ‖fderiv ℝ (e ∘ P) y‖ ≤ K) ∧
      ∀ q : M, dist (e q) (e p) < δ →
        ‖L (e q - e p)‖ < ρ / 4 ∧ P (L (e q - e p)) = q := by
  obtain ⟨L, P, hP0, hP, hinv⟩ := m65Embedding_exists_linear_chart e he hinj p
  have hP1 : ContMDiffAt (𝓡 3) (𝓡 3) 1 P 0 := hP.of_le (by simp)
  obtain ⟨W, hW, hPOn⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hP1
  have heP : ContDiffAt ℝ ∞ (e ∘ P) 0 :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp 0 hP)
  let K := ‖fderiv ℝ (e ∘ P) 0‖ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKn : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      ‖fderiv ℝ (e ∘ P) y‖ < K :=
    ((heP.fderiv_right (m := 0) (by simp)).continuousAt.norm).eventually
      (Iio_mem_nhds (by dsimp only [K]; linarith))
  obtain ⟨η, hη, hηW⟩ := Metric.mem_nhds_iff.mp (inter_mem hW hKn)
  let ρ := η / 3
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hPin : ContMDiffOn (𝓡 3) (𝓡 3) 1 P (ball 0 (2 * ρ)) :=
    hPOn.mono (fun y hy => (hηW (by
      apply ball_subset_ball (show 2 * ρ ≤ η by dsimp only [ρ]; linarith) hy)).1)
  have hDbound (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ closedBall 0 ρ) :
      ‖fderiv ℝ (e ∘ P) y‖ ≤ K :=
    (hηW ((closedBall_subset_ball (by dsimp only [ρ]; linarith)) hy)).2.le
  have hinv' : ∀ᶠ z in 𝓝 (e p), ∀ q : M, e q = z → P (L (e q - e p)) = q := by
    rw [hemb.isInducing.nhds_eq_comap p, Filter.eventually_comap] at hinv
    exact hinv
  have hLsmall : ∀ᶠ z in 𝓝 (e p), ‖L (z - e p)‖ < ρ / 4 := by
    have hc : Continuous (fun z => ‖L (z - e p)‖) :=
      (L.continuous.comp (continuous_id.sub continuous_const)).norm
    have hsmall : ‖L (e p - e p)‖ < ρ / 4 := by
      simpa only [sub_self, map_zero, norm_zero] using (show 0 < ρ / 4 by positivity)
    exact hc.continuousAt.eventually (Iio_mem_nhds hsmall)
  obtain ⟨δ, hδ, hδcap⟩ := Metric.mem_nhds_iff.mp (inter_mem hinv' hLsmall)
  refine ⟨L, P, ρ, δ, K, hρ, hδ, hK, hP0, hPin, hDbound, ?_⟩
  intro q hq
  have h := hδcap (show e q ∈ ball (e p) δ from hq)
  exact ⟨h.2, h.1 q rfl⟩

end PoincareConjecture
