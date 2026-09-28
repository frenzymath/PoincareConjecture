import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CurvatureJets
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.ControlledCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, ℝ → RiemannianMetric n (M k)} {p : ∀ k, M k}
    {T' T : ℝ} {r R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover (g k) (p k)
      T' T (r j) (R j) (ρ j) (a j) (b j) (N j))

local instance : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩

theorem exists_partial_metric_limit_of_normal_covers
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (ha : ∀ j, 0 < a j)
    (htime : 0 ∈ Ioo T' T)
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    {A : ℝ} (hA : 0 < A)
    (hmargin : ∀ j, r j + ρ j / 2 < A)
    (hcofinal : ∀ B : ℝ, B < A → ∃ j, B < r j)
    (hraw : ∀ j m, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ hjk : j ≤ k,
      (cover k j hjk).HasMetricJetBound m B) :
    Nonempty (PartialPointedMetricConvergence (fun k => g k 0) p A) := by
  choose L c hc he hlower using
    partialUnitBallMap_distance_bounds cover hdist hρ ha
  have hconn (k : ℕ) (x : M k) (s : ℝ) : IsPreconnected (ball x s) := by
    rw [metric_ball_eq_of_riemannian_edist hdist]
    exact (g k 0).isPreconnected_ball x s
  have hradius : ∀ i (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1),
      ∃ B : ℝ, B < A ∧ ∀ᶠ k in atTop,
        dist (partialUnitBallMap cover k 0 ⟨0, by simp⟩)
          (partialUnitBallMap cover k i x) ≤ B := by
    simpa only [partialUnitBallMap_zero] using
      partialUnitBallMap_eventual_radius cover hdist hρ hρR hmargin
  have hcover : ∀ B : ℝ, 0 < B → B < A → ∃ S : Finset ℕ,
      ∃ K : ℕ → Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∀ i ∈ S, IsCompact (K i)) ∧ ∀ᶠ k in atTop,
          ball (partialUnitBallMap cover k 0 ⟨0, by simp⟩) B ⊆
            ⋃ i ∈ S, partialUnitBallMap cover k i '' K i := by
    simpa only [partialUnitBallMap_zero] using
      partialUnitBallMap_compact_cover cover hdist hρ hcofinal
  have helliptic : ∀ i K, IsCompact K →
      K ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g k 0).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (partialUnitBallMap cover k i)) x v v := by
    intro i K _hK hKU
    obtain ⟨a, ha, htail⟩ :=
      partialUnitBallMap_eventually_lower_coefficients cover hρ hρR ha i
    exact ⟨a, ha, htail.mono fun k hk x hx v => hk 0 htime x (hKU hx) v⟩
  have hlimit := ChartDistance.exists_partial_metric_limit_of_controlled_charts
    (fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => isOpen_ball)
    (partialUnitBallMap cover) L (fun k i => he i k) c hc
    (fun k i => hlower i k) (partialUnitBallMap_isOpenEmbedding cover hρ hρR)
    hconn (partialUnitBallMap_isLocalDiffeomorph cover hρ hρR)
    (i₀ := 0) ⟨0, by simp⟩ A hA hradius hcover (fun k => g k 0) hdist
    (partialUnitBallMap_eventually_bounded_derivatives cover hρ hρR hraw) helliptic
  simpa only [partialUnitBallMap_zero] using hlimit

include cover in

theorem exists_partial_metric_limit_of_curvature_and_normal_covers
    (D : ∀ k, LeviCivitaData (g k 0))
    (hr : ∀ j, 0 < r j) (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j < R j)
    (ha : ∀ j, 0 < a j) (htime : 0 ∈ Ioo T' T)
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    {A : ℝ} (hA : 0 < A) (hmargin : ∀ j, r j + R j < A)
    (hcofinal : ∀ B : ℝ, B < A → ∃ j, B < r j)
    (hcurv : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k 0).ball (p k) (r j + R j), (D k).curvatureDerivativeNorm l x ≤ C) :
    Nonempty (PartialPointedMetricConvergence (fun k => g k 0) p A) := by
  have hsmall (j : ℕ) : ρ j / 2 ≤ R j :=
    (half_le_self (hρ j).le).trans (hρR j).le
  apply exists_partial_metric_limit_of_normal_covers cover hρ hsmall ha htime hdist hA
    (fun j => (add_le_add le_rfl (hsmall j)).trans_lt (hmargin j)) hcofinal
  intro j m
  obtain ⟨B, _hB, htail⟩ := eventually_normalCover_jet_bound_of_curvature
    D (hr j) (hρ j) (hρR j) (hcurv j) m
  exact ⟨B, htail.mono fun k hk hjk => hk (cover k j hjk)⟩

end PoincareConjecture.M28
