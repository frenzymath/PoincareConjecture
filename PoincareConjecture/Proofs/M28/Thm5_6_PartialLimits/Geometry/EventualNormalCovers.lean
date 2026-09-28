import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverMetricLimit
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.M28




theorem exists_partial_metric_limit_of_eventual_normal_covers
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, ℝ → RiemannianMetric n (M k)} {p : ∀ k, M k}
    (D : ∀ k, LeviCivitaData (g k 0))
    {T' T : ℝ} {r R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (hr : ∀ j, 0 < r j) (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j < R j)
    (ha : ∀ j, 0 < a j) (htime : 0 ∈ Ioo T' T)
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    {A : ℝ} (hA : 0 < A) (hmargin : ∀ j, r j + R j < A)
    (hcofinal : ∀ B : ℝ, B < A → ∃ j, B < r j)
    (hcurv : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k 0).ball (p k) (r j + R j), (D k).curvatureDerivativeNorm l x ≤ C)
    (hcovers : ∀ j, ∀ᶠ k in atTop,
      Nonempty (NormalChartCover (g k) (p k) T' T
        (r j) (R j) (ρ j) (a j) (b j) (N j))) :
    Nonempty (PartialPointedMetricConvergence (fun k => g k 0) p A) := by
  classical
  obtain ⟨σ, hσ, hstages⟩ := Poincare.exists_strictMono_forall_le_of_eventually hcovers
  let cover : ∀ k j, j ≤ k → NormalChartCover (g (σ k)) (p (σ k))
      T' T (r j) (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk => Classical.choice (hstages k j hjk)
  have hcurv' : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g (σ k) 0).ball (p (σ k)) (r j + R j),
        (D (σ k)).curvatureDerivativeNorm l x ≤ C := by
    intro j l
    obtain ⟨C, hC, htail⟩ := hcurv j l
    exact ⟨C, hC, hσ.tendsto_atTop.eventually htail⟩
  obtain ⟨G⟩ := exists_partial_metric_limit_of_curvature_and_normal_covers
    cover (fun k => D (σ k)) hr hρ hρR ha htime (fun k => hdist (σ k))
    hA hmargin hcofinal hcurv'
  exact ⟨G.reindex hσ⟩

end PoincareConjecture.M28
