import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticControlledCharts
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.NormalChartBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CurvatureJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M30




theorem exists_complete_static_limit_of_normal_covers
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (p : ∀ k, M k)
    (D : ∀ k, LeviCivitaData (g k))
    {R rho : ℕ → ℝ} {N : ℕ → ℕ}
    (hsize : ∀ j, 0 < rho j ∧ 2 * rho j < R j ∧ R j < 1)
    (cover : ∀ k j, j ≤ k → NormalChartCover (fun _ => g k) (p k)
      (-1) 1 ((j : ℝ) + 1) (R j) (rho j) (1 / 4) (9 / 4) (N j))
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hcurv : ∀ j m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k).ball (p k) ((j : ℝ) + 1 + R j),
        (D k).curvatureDerivativeNorm m x ≤ B) :
    ∃ G : PartialPointedMetricConvergence g p 1,
      G.limitCarrier.metricComplete G.limitMetric ∧
        ∀ A : ℝ, 0 < A → ∃ l : ℕ, ∀ᶠ k in atTop,
          (g (G.subsequence k)).ball (p (G.subsequence k)) A ⊆
            G.embedding k '' G.exhaustion l := by
  classical
  let : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
  have hrho (j : ℕ) : 0 < rho j := (hsize j).1
  have hhalf (j : ℕ) : rho j / 2 ≤ R j := by
    linarith [(hsize j).1, (hsize j).2.1]
  have hquarter (j : ℕ) : (0 : ℝ) < (fun _ : ℕ => (1 / 4 : ℝ)) j := by
    norm_num
  let e := M28.partialUnitBallMap cover
  choose L c hc he hlower using
    M28.partialUnitBallMap_distance_bounds cover hdist hrho hquarter
  have hconn (k : ℕ) (x : M k) (r : ℝ) : IsPreconnected (ball x r) := by
    rw [M28.metric_ball_eq_of_riemannian_edist (g := fun k _ => g k) hdist]
    exact (g k).isPreconnected_ball x r
  have hradius (k i : ℕ) (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
      dist (p k) (e k i x) ≤ ((Nat.unpair i).1 : ℝ) + 2 := by
    let j := min (Nat.unpair i).1 k
    let l : Fin (N j + 1) :=
      ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    have hx := normalChart_unitBallMap_mem_ball
      (cover k j (min_le_right _ _)) (hrho j) (hhalf j) l x
    have hpoint : e k i x ∈ (g k).ball (p k) ((j : ℝ) + 1 + rho j / 2) := hx
    rw [← M28.metric_ball_eq_of_riemannian_edist (g := fun k _ => g k) hdist] at hpoint
    have hj : (j : ℝ) ≤ ((Nat.unpair i).1 : ℝ) :=
      Nat.cast_le.mpr (min_le_left _ _)
    have hsmall := hsize j
    have hp : dist (p k) (e k i x) < (j : ℝ) + 1 + rho j / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hpoint
    linarith
  have hb (i j : ℕ) (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (y : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ∃ B : ℝ, ∀ k, dist (e k i x) (e k j y) ≤ B := by
    refine ⟨(((Nat.unpair i).1 : ℝ) + 2) + (((Nat.unpair j).1 : ℝ) + 2), ?_⟩
    intro k
    apply (dist_triangle _ (p k) _).trans
    exact add_le_add (by simpa only [dist_comm] using hradius k i x) (hradius k j y)
  have hcover : ∀ A : ℝ, 0 < A → ∃ s : Finset ℕ,
      ∃ K : ℕ → Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∀ i ∈ s, IsCompact (K i)) ∧ ∀ᶠ k in atTop,
          ball (e k 0 ⟨0, by simp⟩) A ⊆ ⋃ i ∈ s, e k i '' K i := by
    intro A hA
    have hcofinal : ∀ B : ℝ, B < A + 1 → ∃ j : ℕ, B < (j : ℝ) + 1 := by
      intro B _hB
      obtain ⟨j, hj⟩ := exists_nat_gt B
      exact ⟨j, by linarith⟩
    simpa only [e, M28.partialUnitBallMap_zero] using
      M28.partialUnitBallMap_compact_cover cover hdist hrho hcofinal A hA (by linarith)
  have hraw : ∀ j m, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ hjk : j ≤ k,
      (cover k j hjk).HasMetricJetBound m B := by
    intro j m
    obtain ⟨B, _hB, htail⟩ := M28.eventually_normalCover_jet_bound_of_curvature
      (g := fun k _ => g k) (T' := -1) (T := 1)
      D (show (0 : ℝ) < (j : ℝ) + 1 by positivity) (hrho j)
      (show rho j < R j by linarith [(hsize j).1, (hsize j).2.1]) (hcurv j) m
    exact ⟨B, htail.mono fun k hk hjk => hk (cover k j hjk)⟩
  have helliptic : ∀ i K, IsCompact K →
      K ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (e k i)) x v v := by
    intro i K _hK hKU
    obtain ⟨a, ha, htail⟩ :=
      M28.partialUnitBallMap_eventually_lower_coefficients cover hrho hhalf hquarter i
    exact ⟨a, ha, htail.mono fun k hk x hx v => hk 0 (by norm_num) x (hKU hx) v⟩
  have hlimit := exists_complete_static_limit_of_controlled_charts
    (fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => isOpen_ball)
    e L (fun k i => he i k) c hc (fun k i => hlower i k)
    (M28.partialUnitBallMap_isOpenEmbedding cover hrho hhalf) hconn
    (M28.partialUnitBallMap_isLocalDiffeomorph cover hrho hhalf) hb
    (i₀ := 0) ⟨0, by simp⟩ hcover g hdist
    (M28.partialUnitBallMap_eventually_bounded_derivatives cover hrho hhalf hraw) helliptic
  have hbase : (fun k => e k 0 ⟨0, by simp⟩) = p :=
    funext (M28.partialUnitBallMap_zero cover)
  rw [hbase] at hlimit
  simpa only [e, M28.partialUnitBallMap_zero] using hlimit

end PoincareConjecture.M30
