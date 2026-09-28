import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CoordinateMetricLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CountableCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Diagonal
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M28

theorem exists_regular_metric_limit_of_normal_covers
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → RegularNormalChartCover (g k) (p k)
      (δ j) (R j) (ρ j) (N j))
    (Dg : ∀ k, LeviCivitaData (g k))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, 2 * ρ j < R j)
    (hstep : ∀ j, 4 * δ (j + 1) ≤ 2 * δ j)
    (hcofinal : ∀ ε : ℝ, 0 < ε → ∃ j, 4 * δ j ≤ ε)
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hcurv : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (g k) (p k) (2 * δ j),
        (Dg k).curvatureDerivativeNorm l x ≤ C) :
    Nonempty (RegularPointedMetricConvergence g p) := by
  classical
  let U : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun _ => ball 0 1
  let hU : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  let : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n))
      (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : IsManifold (𝓡 n) ∞ (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isOpen_ball.isOpenEmbedding_subtypeVal.isManifold_singleton
  let : LocallyCompactSpace (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isOpen_ball.locallyCompactSpace
  let e := regularUnitBallMap cover
  have hhalf (j : ℕ) : ρ j / 2 ≤ R j := by
    have := hρ j
    have := hρR j
    linarith
  have hfull (j : ℕ) : ρ j < R j := by
    have := hρ j
    have := hρR j
    linarith
  choose L c hc he hlower using regularUnitBallMap_distance_bounds cover hdist hρ
  have hopen := regularUnitBallMap_isOpenEmbedding cover hρ hhalf
  have hsmooth := regularUnitBallMap_isLocalDiffeomorph cover hρ hhalf
  have hconn (k : ℕ) (x : M k) (r : ℝ) : IsPreconnected (ball x r) := by
    rw [metric_ball_eq_of_riemannian_edist (g := fun k _ => g k) hdist]
    exact (g k).isPreconnected_ball x r
  have hjets := regularUnitBallMap_bounded_derivatives_of_curvature cover Dg
    hρ hfull hcurv
  have hsource (i k : ℕ) : ContDiffOn ℝ ∞
      ((g k).pullbackCoefficients
        (ChartDistance.chartParametrization U hU (i := i) (e k i)))
      (U i) := by
    intro x hx
    exact ((g k).contDiffAt_pullbackCoefficients
      ((ChartDistance.contMDiffOn_chartParametrization U hU (i := i) (e := e k i)
        (hsmooth k i).contMDiff).contMDiffAt ((hU i).mem_nhds hx))).contDiffWithinAt
  obtain ⟨σ, hσ, B, hBsmooth, hBjets⟩ := exists_common_smoothSubsequenceExtraction hU
    (fun i k => (g k).pullbackCoefficients
      (ChartDistance.chartParametrization U hU (i := i) (e k i)))
    hsource hjets
  obtain ⟨τ, hτ, D, hD⟩ := ChartDistance.exists_pairwise_limits (fun k => e (σ k))
    L (fun k i => he i (σ k)) (fun i j x y => by
      obtain ⟨C, hC⟩ := regularUnitBallMap_pairwise_bounded cover hdist hρ hρR i j
      exact ⟨C, fun k => hC (σ k) x y⟩)
  let φ := σ ∘ τ
  have hφ : StrictMono φ := hσ.comp hτ
  have hjets' : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => (g (φ k)).pullbackCoefficients
        (ChartDistance.chartParametrization U hU (i := i) (e (φ k) i))) := by
    intro i K hK hKU m
    obtain ⟨C, hC⟩ := hjets i K hK hKU m
    exact ⟨C, hφ.tendsto_atTop.eventually hC⟩
  have helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g (φ k)).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (i := i) (e (φ k) i)) x v v := by
    intro i K _hK hKU
    obtain ⟨a, ha, htail⟩ :=
      regularUnitBallMap_eventually_lower_coefficients cover hρ hhalf i
    refine ⟨a, ha, (hφ.tendsto_atTop.eventually htail).mono fun k hk x hx v => ?_⟩
    exact hk x (hKU hx) v
  have hbound := ChartDistance.locallyEventuallyBoundedDerivatives_source_transition
    U hU (fun i j x y =>
      (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    L (fun k i => he i (φ k)) c hc (fun k i => hlower i (φ k))
    (fun k => hopen (φ k)) (fun k => hconn (φ k)) (fun k => hsmooth (φ k))
    (fun k => g (φ k)) hjets' helliptic
  apply exists_regular_metric_limit_of_coordinate_limits cover hρ hhalf hstep hcofinal
    hφ hD L (fun k i => he i (φ k)) c hc (fun k i => hlower i (φ k))
    hconn hbound B hBsmooth
  · intro i m K hK hKU V hV
    exact hτ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV)
  · intro i x hx
    obtain ⟨a, ha, hbound⟩ := helliptic i {x} isCompact_singleton
      (singleton_subset_iff.mpr hx)
    exact ⟨a, ha, hbound.mono fun _ hk => hk x (mem_singleton x)⟩

theorem exists_regular_metric_limit_of_eventual_normal_covers
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (Dg : ∀ k, LeviCivitaData (g k))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, 2 * ρ j < R j)
    (hstep : ∀ j, 4 * δ (j + 1) ≤ 2 * δ j)
    (hcofinal : ∀ ε : ℝ, 0 < ε → ∃ j, 4 * δ j ≤ ε)
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hcurv : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (g k) (p k) (2 * δ j),
        (Dg k).curvatureDerivativeNorm l x ≤ C)
    (hcovers : ∀ j, ∀ᶠ k in atTop,
      Nonempty (RegularNormalChartCover (g k) (p k) (δ j) (R j) (ρ j) (N j))) :
    Nonempty (RegularPointedMetricConvergence g p) := by
  classical
  obtain ⟨τ, hτ, hτcovers⟩ := Poincare.exists_strictMono_forall_le_of_eventually hcovers
  let cover := fun k j (hjk : j ≤ k) => Classical.choice (hτcovers k j hjk)
  have hcurv' : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (g (τ k)) (p (τ k)) (2 * δ j),
        (Dg (τ k)).curvatureDerivativeNorm l x ≤ C := by
    intro j l
    obtain ⟨C, hC, htail⟩ := hcurv j l
    exact ⟨C, hC, hτ.tendsto_atTop.eventually htail⟩
  obtain ⟨G⟩ := exists_regular_metric_limit_of_normal_covers cover (fun k => Dg (τ k))
    hρ hρR hstep hcofinal (fun k => hdist (τ k)) hcurv'
  exact ⟨G.reindex hτ⟩

end PoincareConjecture.M28
