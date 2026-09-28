import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticTolerance
import Mathlib.Geometry.Manifold.LocalDiffeomorph










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

open M34 SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "J4" => Jet E (MetricCoefficient 3) 4

noncomputable local instance capAnalyticCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capAnalyticCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace



theorem limitCanonical_partial_chart_scalarAnalytic
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {x : E} (hx : x ∈ f.source) :
    scalarAnalyticJet 3 (spatialJet 4
      (fun z : ℝ × E => g.pullbackCoefficients f z.2) (0, x)) =
        (D.scalarCurvature (f x), scalarGradientNorm g D (f x),
          D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) := by
  have hinj (y : E) (hy : y ∈ f.source) :
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := by
    have hlocal := f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy
    exact (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  simpa only [one_smul, Real.one_rpow, one_pow, div_one] using
    cap_analyticJet_normalizedPullback g D f.open_source f.contMDiffOn_toFun hinj
      (by norm_num : (0 : ℝ) < 1) hx



theorem limitCanonical_eventually_actual_analytic_error
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {g : ∀ k, RiemannianMetric 3 (M k)} (D : ∀ k, LeviCivitaData (g k))
    {h : RiemannianMetric 3 X} (D0 : LeviCivitaData h)
    (f : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M k) ∞)
    (f0 : PartialDiffeomorph (𝓡 3) (𝓡 3) E X ∞)
    {K : Set E} (hK : IsCompact K) (hK0 : K ⊆ f0.source)
    (hsource : ∀ᶠ k in atTop, K ⊆ (f k).source)
    (hjet : ∀ j ≤ 4, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients (f k)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients f0)) atTop K)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖((D k).scalarCurvature (f k x), scalarGradientNorm (g k) (D k) (f k x),
          (D k).laplacian (D k).scalarCurvature (f k x) + 2 * (D k).ricciNormSq (f k x)) -
        (D0.scalarCurvature (f0 x), scalarGradientNorm h D0 (f0 x),
          D0.laplacian D0.scalarCurvature (f0 x) + 2 * D0.ricciNormSq (f0 x))‖ ≤ eta := by
  let B0 := h.pullbackCoefficients f0
  have hB0 : ContDiffOn ℝ ∞ B0 f0.source := by
    intro x hx
    exact (h.contDiffAt_pullbackCoefficients
      (f0.contMDiffOn_toFun.contMDiffAt (f0.open_source.mem_nhds hx))).contDiffWithinAt
  let J0 : E → J4 := fun x => spatialJet 4 (fun z : ℝ × E => B0 z.2) (0, x)
  have hJ0 : ContinuousOn J0 K := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro j
    exact (hB0.contDiffAt (f0.open_source.mem_nhds (hK0 hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)
  have hcompact : IsCompact (J0 '' K) := hK.image_of_continuousOn hJ0
  have hinv : J0 '' K ⊆ curvatureJetDomain 3 2 := by
    rintro _ ⟨x, hx, rfl⟩
    change ((twoJetProjection 3 (baseProjection 2 2
      (spatialJet 4 (fun z : ℝ × E => B0 z.2) (0, x)))).1).IsInvertible
    rw [baseProjection_spatialJet, twoJetProjection_spatialJet]
    have hlocal := f0.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hK0 hx)
    exact h.isInvertible_pullbackCoefficients
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  obtain ⟨delta, hdelta, hbound⟩ := exists_uniform_cap_analyticJet_tolerance
    hcompact hinv heta
  have htail : ∀ᶠ k in atTop, ∀ j : Fin 5, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ (j : ℕ) ((g k).pullbackCoefficients (f k)) x -
        iteratedFDeriv ℝ (j : ℕ) B0 x‖ ≤ delta := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hjet j (by omega))) delta hdelta]
      with k hk x hx
    have hh := hk x hx
    rw [dist_comm, dist_eq_norm] at hh
    exact hh.le
  filter_upwards [hsource, htail] with k hs hk x hx
  have hnear : ‖spatialJet 4
      (fun z : ℝ × E => (g k).pullbackCoefficients (f k) z.2) (0, x) - J0 x‖ ≤ delta := by
    apply (pi_norm_le_iff_of_nonneg hdelta.le).mpr
    intro j
    exact hk j x hx
  have hread := (hbound (J0 x) (mem_image_of_mem J0 hx)
    (spatialJet 4 (fun z : ℝ × E => (g k).pullbackCoefficients (f k) z.2) (0, x)) hnear).2
  dsimp only [J0, B0] at hread
  rwa [limitCanonical_partial_chart_scalarAnalytic (D k) (f k) (hs hx),
    limitCanonical_partial_chart_scalarAnalytic D0 f0 (hK0 hx)] at hread

end PoincareConjecture.M47
