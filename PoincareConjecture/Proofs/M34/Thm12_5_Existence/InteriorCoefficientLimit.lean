import PoincareConjecture.Proofs.M34.Thm12_5_Existence.LocalInteriorExtraction
import PoincareConjecture.Proofs.M34.Mathlib.CompatibleSmoothLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds



structure InteriorCoefficientLimit {g0 : StandardInitialMetric}
    (A : CompactCapApproximation g0) where

  subsequence : ℕ → ℕ

  strictMono : StrictMono subsequence

  coefficients : ℝ × StandardCapSpace → MetricCoefficient 3

  smooth : ContDiffOn ℝ ∞ coefficients (Ioo 0 A.time ×ˢ univ)

  jet_convergence : ∀ m K, IsCompact K → K ⊆ Ioo 0 A.time ×ˢ univ →
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun p : ℝ × StandardCapSpace => A.coefficients (subsequence k) p.1 p.2))
      (iteratedFDeriv ℝ m coefficients) atTop K



theorem interiorCoefficientLimit_exists {g0 : StandardInitialMetric}
    (A : CompactCapApproximation g0) (P : RicciFlowCurvatureTheory.{0}) :
    Nonempty (InteriorCoefficientLimit A) := by
  obtain ⟨σ, hσ, F, hF, hconv⟩ := A.exists_local_interior_limits P
  have hcompact (K : Set (ℝ × StandardCapSpace)) (hK : IsCompact K)
      (hKΩ : K ⊆ Ioo 0 A.time ×ˢ univ) : ∃ i, K ⊆ A.interiorBallDomain i := by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := Prod.snd)
      continuous_snd.continuousOn
    obtain ⟨i, hi⟩ := exists_nat_gt B
    refine ⟨i, ?_⟩
    intro p hp
    refine ⟨(hKΩ hp).1, ?_⟩
    simp only [Metric.mem_ball, dist_zero_right]
    linarith [hB p hp]
  have hcover (p : ℝ × StandardCapSpace) (hp : p ∈ Ioo 0 A.time ×ˢ univ) :
      ∃ i, p ∈ A.interiorBallDomain i := by
    obtain ⟨i, hi⟩ := hcompact {p} isCompact_singleton (singleton_subset_iff.mpr hp)
    exact ⟨i, hi (mem_singleton p)⟩
  obtain ⟨G, hG, hGconv⟩ := exists_contDiffOn_limit_of_open_exhaustion
    (Ω := Ioo 0 A.time ×ˢ (univ : Set StandardCapSpace))
    (A.interiorBallDomain_isOpen) (fun _ _ hp => ⟨hp.1, mem_univ _⟩)
    hcover hcompact hF hconv
  exact ⟨{
    subsequence := σ
    strictMono := hσ
    coefficients := G
    smooth := hG
    jet_convergence := hGconv }⟩

end PoincareConjecture.M34
