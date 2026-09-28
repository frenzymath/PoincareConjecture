import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem isCompact_closure_initial_ball_of_terminal_buffer
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] (g : RiemannianMetric n M) (p : M)
    (U : TopologicalSpace.Opens M) {A R T B : ℝ}
    (hT : 0 < T) (hA : 0 < A) (hAR : A < R)
    (hU : (U : Set M) = g.ball p R)
    (G : RicciFlow n U (Icc (-T) 0))
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      (G.metric 0).inner x v w = g.inner x.val
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (hcurv : ∀ s ∈ Icc (-T) 0, ∀ y : U,
      (G.connection s).curvatureTensorNorm y ≤ B)
    (hcompact : IsCompact (closure (g.ball p ((A + R) / 2))))
    (x : U) (hx : x.val ∈ g.ball p A) :
    IsCompact (closure ((G.metric (-T)).ball x
      ((R - A) / (2 * Real.exp ((n : ℝ) ^ 3 * max B 1 * T))))) := by
  let K : ℝ := max B 1
  let L : ℝ := (n : ℝ) ^ 3 * K
  let E : ℝ := Real.exp (L * T)
  let r : ℝ := (R - A) / (2 * E)
  let ρ : ℝ := (A + R) / 2
  have hE : 0 < E := Real.exp_pos _
  have hr : 0 < r := div_pos (sub_pos.mpr hAR) (mul_pos (by norm_num) hE)
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hR : 0 < R := hA.trans hAR
  have hEr : E * r = (R - A) / 2 := by
    dsimp only [r]
    field_simp [hE.ne']
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hRic (s : ℝ) (hs : s ∈ Icc (-T) 0) (y : U)
      (v : TangentSpace (𝓡 n) y) :
      |(G.connection s).ricci y v v| ≤ L * (G.metric s).inner y v v := by
    have hQ : 0 ≤ (G.metric s).inner y v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((G.metric s).pos y v hv).le
    have hnorm := (G.connection s).abs_ricci_quadratic_le_curvatureTensorNorm y v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) y) = n :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((hcurv s hs y).trans (le_max_left B 1))
        (by positivity)) hQ)
  have hcompare : (G.metric (-T)).ball x r ⊆ (G.metric 0).ball x (E * r) := by
    have h := G.ball_subset_ball_of_ricci_bound (convex_Icc (-T) 0) (Subset.refl _)
      x r L (s := -T) (t := 0) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
      (fun s hs y _ v => hRic s hs y v)
    simpa only [zero_sub, neg_neg, abs_of_nonneg hT.le] using h
  have hbuffer : closure (g.ball p ρ) ⊆ U := by
    have hclosed : IsClosed {y : M | edist p y ≤ ENNReal.ofReal ρ} :=
      isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hsub : g.ball p ρ ⊆ {y : M | edist p y ≤ ENNReal.ofReal ρ} := by
      intro y hy
      change edist p y < ENNReal.ofReal ρ at hy
      exact hy.le
    intro y hy
    rw [hU]
    exact (closure_minimal hsub hclosed hy).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hρR)
  let Q : Set U := (Subtype.val : U → M) ⁻¹' closure (g.ball p ρ)
  have hQcompact : IsCompact Q :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact
      (fun y hy => ⟨⟨y, hbuffer hy⟩, rfl⟩)
  have hQclosed : IsClosed Q := isClosed_closure.preimage continuous_subtype_val
  apply hQcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ hQclosed
  intro y hy
  apply subset_closure
  have hxy : edist x.val y.val < ENNReal.ofReal (E * r) :=
    ((G.metric 0).edist_map_le_of_metric_pullback g contMDiff_subtype_val hmetric x y).trans_lt
      (hcompare hy)
  change edist p y.val < ENNReal.ofReal ρ
  calc
    edist p y.val ≤ edist p x.val + edist x.val y.val := edist_triangle _ _ _
    _ < ENNReal.ofReal A + ENNReal.ofReal (E * r) := ENNReal.add_lt_add hx hxy
    _ = ENNReal.ofReal ρ := by
      rw [← ENNReal.ofReal_add hA.le (mul_pos hE hr).le, hEr]
      congr 1
      dsimp [ρ]
      ring

end PoincareConjecture.M30
