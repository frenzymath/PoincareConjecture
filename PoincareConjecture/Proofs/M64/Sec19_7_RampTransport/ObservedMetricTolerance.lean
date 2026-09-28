import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CompactRetractionMetric














set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64.RampTransport




theorem exists_observed_metric_tolerance
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : RiemannianMetric n M)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p q : M,
      ‖e p - e q‖ < delta → g.edist p q < ENNReal.ofReal epsilon := by
  have hK : IsCompact (range e) := isCompact_range he.continuous
  obtain ⟨C, hC, V, hV, hdiag, hmetric⟩ := compact_metric_control_near_diagonal
    g hK hU heU (hrho.of_le (by simp))
  let diagonal := fun z : W => (z, z)
  have hdiagonal : IsCompact (diagonal '' range e) :=
    hK.image (continuous_id.prodMk continuous_id)
  have hsub : diagonal '' range e ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hdiag z hz
  obtain ⟨eta, heta, hthick⟩ := hdiagonal.exists_thickening_subset_open hV hsub
  let delta := min (eta / 2) (epsilon / C)
  have hdelta : 0 < delta := lt_min (half_pos heta) (div_pos hepsilon hC)
  have hdeta : delta < eta := (min_le_left _ _).trans_lt (half_lt_self heta)
  refine ⟨delta, hdelta, ?_⟩
  intro p q hpq
  have hpair : (e p, e q) ∈ V := by
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨diagonal (e p), mem_image_of_mem diagonal (mem_range_self p), ?_⟩
    rw [dist_eq_norm]
    change max ‖e p - e p‖ ‖e q - e p‖ < eta
    rw [sub_self, norm_zero, norm_sub_rev (e q) (e p)]
    exact max_lt heta (hpq.trans hdeta)
  have hbound : C * ‖e p - e q‖ < epsilon := by
    calc
      C * ‖e p - e q‖ < C * delta := mul_lt_mul_of_pos_left hpq hC
      _ ≤ C * (epsilon / C) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = epsilon := by field_simp
  have h := hmetric (e p, e q) hpair
  rw [hre, hre] at h
  exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hepsilon).mpr hbound)

end PoincareConjecture.M64.RampTransport
