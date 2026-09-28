import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.SpacetimeBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.FiniteDimensional











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricFlowApproximation

open SpacetimeBounds

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)] (A : MetricFlowApproximation ginit Mfamily)



def interiorBallDomain (i : ℕ) : Set (ℝ × StandardCapSpace) :=
  Ioo 0 A.time ×ˢ Metric.ball 0 ((i : ℝ) + 1)


theorem interiorBallDomain_isOpen (i : ℕ) : IsOpen (A.interiorBallDomain i) :=
  isOpen_Ioo.prod Metric.isOpen_ball

set_option synthInstance.maxHeartbeats 100000 in




theorem exists_local_interior_limits (P : RicciFlowCurvatureTheory.{0}) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ F : ℕ → ℝ × StandardCapSpace → MetricCoefficient 3,
        (∀ i, ContDiffOn ℝ ∞ (F i) (A.interiorBallDomain i)) ∧
          ∀ i m K, IsCompact K → K ⊆ A.interiorBallDomain i →
            TendstoUniformlyOn
              (fun k => iteratedFDeriv ℝ m
                (fun p : ℝ × StandardCapSpace => A.coefficients (σ k) p.1 p.2))
              (iteratedFDeriv ℝ m (F i)) atTop K := by
  classical
  have htail (i : ℕ) : ∃ N : ℕ, ∀ k ≥ N,
      Metric.closedBall (0 : StandardCapSpace) ((i : ℝ) + 1) ⊆ A.source k :=
    eventually_atTop.mp (A.compact_sources _ (isCompact_closedBall _ _))
  choose N hN using htail
  let f : ℕ → ℕ → ℝ × StandardCapSpace → MetricCoefficient 3 :=
    fun i k p => A.coefficients (max k (N i)) p.1 p.2
  have hsource (i k : ℕ) {x : StandardCapSpace}
      (hx : x ∈ Metric.ball 0 ((i : ℝ) + 1)) :
      x ∈ A.source (max k (N i)) :=
    hN i _ (le_max_right _ _) (Metric.ball_subset_closedBall hx)
  have hf (i k : ℕ) : ContDiffOn ℝ ∞ (f i k) (A.interiorBallDomain i) :=
    (A.contDiffOn_interior_coefficients (max k (N i))).mono
      (fun _ hp => ⟨hp.1, hsource i k hp.2⟩)
  have hb (i : ℕ) (K : Set (ℝ × StandardCapSpace)) (hK : IsCompact K)
      (hKU : K ⊆ A.interiorBallDomain i) (m : ℕ) :
      ∃ B : ℝ, ∀ᶠ k : ℕ in atTop, ∀ p ∈ K, ‖iteratedFDeriv ℝ m (f i k) p‖ ≤ B := by
    obtain ⟨B, _hB, hbound⟩ := A.eventually_compact_spacetimeJet_bound P
      (hK.image continuous_snd) m
    refine ⟨B, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop (N i)] with k hk hki p hp
    have hs : p.2 ∈ A.source k :=
      hN i k hki (Metric.ball_subset_closedBall (hKU hp).2)
    simpa only [f, max_eq_left hki] using
      hk p.1 (hKU hp).1 p.2 (mem_image_of_mem Prod.snd hp) hs
  obtain ⟨σ, hσ, F, hF, hconv⟩ :=
    Poincare.Analysis.Calculus.exists_common_smoothSubsequenceExtraction_finiteDimensional
      (E := fun _ => ℝ × StandardCapSpace) (F := fun _ => MetricCoefficient 3)
      (A.interiorBallDomain_isOpen) f hf hb
  refine ⟨σ, hσ, F, hF, ?_⟩
  intro i m K hK hKU
  apply (hconv i m K hK hKU).congr
  filter_upwards [hσ.tendsto_atTop.eventually (eventually_ge_atTop (N i))] with k hk
  intro p _hp
  simp only [f, max_eq_left hk]

end PoincareConjecture.M34.MetricFlowApproximation
