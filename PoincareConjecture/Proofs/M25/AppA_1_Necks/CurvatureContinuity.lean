import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitCurvature











set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture



noncomputable def RiemannianMetric.m25_scalarMetricTwoJet
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) {ι : Type*}
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n))) :
    (r : Fin 3) → ι → ι →
      ContinuousMultilinearMap ℝ (fun _ : Fin r.val => EuclideanSpace ℝ (Fin n)) ℝ :=
  fun r i j => iteratedFDeriv ℝ r.val (fun y => g.inner y (b i) (b j)) x




theorem LeviCivitaData.m25_exists_scalar_ricci_control_of_metric_twoJet
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n))) {α : ℝ} (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D' : LeviCivitaData h),
      (∀ r : ℕ, r ≤ 2 → ∀ i j : ι,
        ‖iteratedFDeriv ℝ r (fun y => h.inner y (b i) (b j)) x -
          iteratedFDeriv ℝ r (fun y => g.inner y (b i) (b j)) x‖ < δ) →
      |D'.scalarCurvature x - D.scalarCurvature x| < α ∧
        ∀ i j : ι, |D'.ricci x (b i) (b j) - D.ricci x (b i) (b j)| < α := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let Data := (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) × LeviCivitaData h
  let J := fun p : Data => p.1.m25_scalarMetricTwoJet x b
  let L := Filter.comap J (𝓝 (g.m25_scalarMetricTwoJet x b))
  have hJ : Tendsto J L (𝓝 (g.m25_scalarMetricTwoJet x b)) := tendsto_comap
  have hjets (r : ℕ) (hr : r ≤ 2) (i j : ι) :
      Tendsto (fun p : Data => iteratedFDeriv ℝ r
        (fun y => p.1.inner y (b i) (b j)) x) L
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b i) (b j)) x)) := by
    let k : Fin 3 := ⟨r, by omega⟩
    exact ((continuous_apply j).tendsto _).comp
      (((continuous_apply i).tendsto _).comp
        (((continuous_apply k).tendsto _).comp hJ))
  let F := fun p : Data =>
    (p.2.scalarCurvature x, fun i j : ι => p.2.ricci x (b i) (b j))
  let y₀ := (D.scalarCurvature x, fun i j : ι => D.ricci x (b i) (b j))
  have hF : Tendsto F L (𝓝 y₀) :=
    (LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets
      (fun p : Data => p.2) D x b hjets).prodMk_nhds
      (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
        LeviCivitaData.tendsto_ricci_of_scalar_metric_jets
          (fun p : Data => p.2) D x (b i) (b j) b hjets)
  obtain ⟨δ, hδ, hbound⟩ := (Metric.nhds_basis_ball.comap J).mem_iff.mp
    (hF (Metric.ball_mem_nhds y₀ hα))
  refine ⟨δ, hδ, ?_⟩
  intro h D' hj
  have hclose : J ⟨h, D'⟩ ∈ Metric.ball (g.m25_scalarMetricTwoJet x b) δ := by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro r
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [dist_pi_lt_iff hδ]
    intro j
    simpa only [dist_eq_norm, J, RiemannianMetric.m25_scalarMetricTwoJet] using
      hj r.val (by omega) i j
  have h := hbound hclose
  simpa only [Set.mem_preimage, Metric.mem_ball, F, y₀, Prod.dist_eq,
    max_lt_iff, dist_pi_lt_iff hα, Real.dist_eq] using h

end PoincareConjecture
