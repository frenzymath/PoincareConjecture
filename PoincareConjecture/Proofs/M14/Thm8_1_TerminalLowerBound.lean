import PoincareConjecture.Proofs.M14.Sec6_7_DisjointImages
import PoincareConjecture.Proofs.M14.Mathlib.IntegralLowerBound









set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}



theorem terminal_density_lower_bound (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) {l₀ : ℝ}
    (hl : ∀ Z ∈ W, M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) ≤ l₀)
    {q : (G.slices (T - τ)).Point} (hq : q ∈ H.endpoint_slice_map '' W) :
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-l₀) ≤ A.density q := by
  obtain ⟨Z, hZ, rfl⟩ := hq
  rw [A.density_eq _ ⟨Z, hW hZ, rfl⟩]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg H.tau_pos.le _)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  rw [H.endpoint_slice_map_val Z (hW hZ)]
  exact hl Z hZ



theorem terminal_reducedVolume_lower_bound (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hm : MeasurableSet W)
    {l₀ V : ℝ}
    (hl : ∀ Z ∈ W, M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) ≤ l₀)
    (hV : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
        (H.endpoint_slice_map '' W)) :
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-l₀) * V ≤
      M14ReducedVolumeOnAnalyticCarrier A W := by
  apply MeasureTheory.mul_le_setIntegral_of_measure_le
    (mul_nonneg (Real.rpow_nonneg H.tau_pos.le _) (Real.exp_pos _).le)
    (A.density_integrable.mono_set (Set.image_mono hW)) hV
  apply (MeasureTheory.ae_restrict_iff' (stable_slice_image_measurable H hW hm)).mpr
  exact Filter.Eventually.of_forall (fun _ hq => terminal_density_lower_bound H A hW hl hq)




theorem terminal_lower_bound_and_earlier (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    (hanalytic : ∀ (σ : ℝ) (Hσ : M14StableSet G T σ x E),
      Nonempty (M14ReducedVolumeAnalyticData G T σ x E Hσ))
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hne : W.Nonempty)
    (hopen : IsOpen W) (hm : MeasurableSet W) {l₀ V : ℝ}
    (hl : ∀ Z ∈ W, M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) ≤ l₀)
    (hV : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
        (H.endpoint_slice_map '' W)) :
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-l₀) * V ≤
        M14ReducedVolumeOnAnalyticCarrier A W ∧
      ∀ σ, 0 < σ → σ ≤ τ →
        ∃ Hσ : M14StableSet G T σ x E,
          W ⊆ Hσ.carrier ∧
          ∃ Aσ : M14ReducedVolumeAnalyticData G T σ x E Hσ,
            Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-l₀) * V ≤
              M14ReducedVolumeOnAnalyticCarrier Aσ W := by
  have hlower := terminal_reducedVolume_lower_bound H A hW hm hl hV
  refine ⟨hlower, ?_⟩
  intro σ hσ hστ
  have hmin : ∀ Z ∈ W,
      ∃ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z), M14IsMinimizing p := by
    intro Z hZ
    obtain ⟨p, _, hp, _⟩ := H.minimizing_path Z (hW hZ)
    exact ⟨p, hp⟩
  obtain ⟨Hσ, hWσ, hmono⟩ := A.fixed_W_monotone W hW hne hopen hm hmin σ hσ hστ
  obtain ⟨Aσ⟩ := hanalytic σ Hσ
  refine ⟨Hσ, hWσ, Aσ, ?_⟩
  rw [analyticCarrier_eq_densityIntegral Hσ Aσ hWσ hm]
  exact hlower.trans hmono

end PoincareConjecture.M14
