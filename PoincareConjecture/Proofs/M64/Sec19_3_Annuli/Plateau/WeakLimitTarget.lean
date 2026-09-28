import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedCompactness
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]




theorem m64Annulus_observed_target_subsequence {m : ℕ}
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C) :
    ∃ (hU : ∀ j, MemLp ((interior m64AnnulusDomain).indicator (e ∘ f j)) 2 volume)
      (u : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure LoopPlane)) (k : ℕ → ℕ),
      StrictMono k ∧ Tendsto (fun j => (hU (k j)).toLp
        ((interior m64AnnulusDomain).indicator (e ∘ f (k j)))) atTop (𝓝 u) ∧
      ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
        Tendsto (fun j => e (f (k j) p)) atTop (𝓝 (u p)) ∧ u p ∈ range e := by
  obtain ⟨hU, u, k, hk, hu⟩ := m64Annulus_observed_strong_subsequence g e he f hf hC
  obtain ⟨l, hl, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ p ∂volume, ∀ j,
      ((hU (k (l j))).toLp ((interior m64AnnulusDomain).indicator (e ∘ f (k (l j))))) p =
        (interior m64AnnulusDomain).indicator (e ∘ f (k (l j))) p :=
    ae_all_iff.mpr (fun j => (hU (k (l j))).coeFn_toLp)
  refine ⟨hU, u, k ∘ l, hk.comp hl, hu.comp hl.tendsto_atTop, ?_⟩
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_of_ae hcoe,
    ae_restrict_mem isOpen_interior.measurableSet] with p hp hrep hpS
  have heq : (fun j => ((hU (k (l j))).toLp
      ((interior m64AnnulusDomain).indicator (e ∘ f (k (l j))))) p) =
        (fun j => e (f (k (l j)) p)) := by
    funext j
    rw [hrep j, indicator_of_mem hpS]
    rfl
  rw [heq] at hp
  exact ⟨hp, (isCompact_range he.continuous).isClosed.mem_of_tendsto hp
    (Eventually.of_forall fun j => mem_range_self (f (k (l j)) p))⟩

end PoincareConjecture
