import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.UniformNormalCover
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.EventualNormalCovers












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M28




theorem exists_partial_metric_limit_of_local_geometry
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    [∀ k, SecondCountableTopology (M k)] [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (D : ∀ k, LeviCivitaData (g k))
    (p : ∀ k, M k) (hn : 1 ≤ n)
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    {A : ℝ} (hA : 0 < A) {r S δ K v V : ℕ → ℝ}
    (hr : ∀ j, 0 < r j) (hδ : ∀ j, 0 < δ j) (hK : ∀ j, 0 ≤ K j)
    (hv : ∀ j, 0 < v j) (hV : ∀ j, 0 ≤ V j)
    (hmargin : ∀ j, r j + 2 * δ j ≤ S j) (hSA : ∀ j, S j < A)
    (hcofinal : ∀ B : ℝ, B < A → ∃ j, B < r j)
    (hgeometry : ∀ j, ∀ᶠ k in atTop,
      IsCompact (closure ((g k).ball (p k) (S j))) ∧
        (∀ x ∈ (g k).ball (p k) (S j), (D k).curvatureTensorNorm x ≤ K j) ∧
        (∀ q ∈ (g k).ball (p k) (r j),
          ENNReal.ofReal (v j) ≤ (g k).volumeMeasure ((g k).ball q (δ j))) ∧
        (g k).volumeMeasure ((g k).ball (p k) (S j)) ≤ ENNReal.ofReal (V j))
    (hcurv : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k).ball (p k) (S j), (D k).curvatureDerivativeNorm l x ≤ C) :
    Nonempty (PartialPointedMetricConvergence g p A) := by
  classical
  choose R ρ N hρ hρR hRδ hfactory using fun j =>
    exists_uniform_normalCover_of_local_noncollapse n hn (hK j) (hδ j) (hv j) (hV j)
  have hcovers : ∀ j, ∀ᶠ k in atTop,
      Nonempty (NormalChartCover (fun _ => g k) (p k) (-1) 1
        (r j) (R j) (ρ j) (1 / 4) (9 / 4) (N j)) := by
    intro j
    filter_upwards [hgeometry j] with k hk
    exact hfactory j (M k) (g k) (D k) (p k) (r j) (S j) (hr j) (hmargin j)
      hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
  have hRS (j : ℕ) : r j + R j < S j := by
    have h1 := hRδ j
    have h2 := hδ j
    have h3 := hmargin j
    linarith
  have hcurv' : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k).ball (p k) (r j + R j), (D k).curvatureDerivativeNorm l x ≤ C := by
    intro j l
    obtain ⟨C, hC, htail⟩ := hcurv j l
    refine ⟨C, hC, htail.mono fun k hk x hx => hk x ?_⟩
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (hRS j).le)
  exact exists_partial_metric_limit_of_eventual_normal_covers (g := fun k _ => g k)
    D hr hρ (fun j => by have := hρR j; have := hρ j; linarith)
    (fun _ => by norm_num) (by constructor <;> norm_num) hdist hA
    (fun j => (hRS j).trans (hSA j)) hcofinal hcurv' hcovers

end PoincareConjecture.M28
