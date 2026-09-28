import PoincareConjecture.Proofs.M47.TerminalCurvatureChartScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

open M34 SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_eventually_scalar_on_finite_cover
    {ι : Type*} [Finite ι]
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (D : LeviCivitaData h)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) (M k) X ∞)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hKtarget : ∀ i, K i ⊆ (c i).target)
    (hsource : ∀ i, ∀ᶠ k in atTop, K i ⊆ ((psi k).trans (c i)).target)
    (hjet : ∀ i j, j ≤ 2 → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients
        ((psi k).trans (c i)).symm))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop (K i))
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ Dk : LeviCivitaData (g k), ∀ z ∈ (psi k).source,
      (∃ i, psi k z ∈ (c i).source ∧ c i (psi k z) ∈ K i) →
      |D.scalarCurvature (psi k z) - Dk.scalarCurvature z| < eta := by
  have hscalar (i : ι) : ∀ᶠ k in atTop, ∀ x ∈ K i,
      |scalarTwoJet (metricTwoJet ((g k).pullbackCoefficients
          ((psi k).trans (c i)).symm) x) -
        scalarTwoJet (metricTwoJet (h.pullbackCoefficients (c i).symm) x)| < eta := by
    have hsmooth : ContDiffOn ℝ ∞ (h.pullbackCoefficients (c i).symm) (c i).target := by
      intro x hx
      exact (h.contDiffAt_pullbackCoefficients
        ((c i).contMDiffOn_invFun.contMDiffAt
          ((c i).open_target.mem_nhds hx))).contDiffWithinAt
    have hinv : ∀ x ∈ (c i).target,
        (h.pullbackCoefficients (c i).symm x).IsInvertible := by
      intro x hx
      have hlocal := (c i).symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx
      exact h.isInvertible_pullbackCoefficients
        (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
    exact terminalCurvature_eventually_uniform_scalar_jet_error
      (c i).open_target (hK i) (hKtarget i) hsmooth hinv (hjet i) heta
  filter_upwards [Filter.eventually_all.mpr hsource, Filter.eventually_all.mpr hscalar]
    with k hksource hkscalar Dk z hz hcover
  obtain ⟨i, hi, hxi⟩ := hcover
  have hci : z ∈ ((psi k).trans (c i)).source := ⟨hz, hi⟩
  have herr := hkscalar i _ hxi
  have hi0 : (c i).symm (c i (psi k z)) = psi k z := (c i).left_inv hi
  have hik : ((psi k).trans (c i)).symm (c i (psi k z)) = z :=
    ((psi k).trans (c i)).left_inv hci
  rw [terminalCurvature_partial_chart_scalar Dk _ (hksource i hxi),
    terminalCurvature_partial_chart_scalar D _ (hKtarget i hxi), hik, hi0] at herr
  rwa [abs_sub_comm] at herr

end PoincareConjecture.M47
