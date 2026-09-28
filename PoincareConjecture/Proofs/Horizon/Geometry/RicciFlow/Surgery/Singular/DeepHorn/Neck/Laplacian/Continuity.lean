import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Laplacian.MetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Laplacian.Operator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

noncomputable section
set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

theorem LeviCivitaData.tendsto_scalar_laplacian_of_four_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (hjets : ∀ r : ℕ, r ≤ 4 → ∀ a c : Fin n,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).laplacian (Dseq i).scalarCurvature x) l
      (𝓝 (D.laplacian D.scalarCurvature x)) := by
  obtain ⟨hmetric, hmetric', _⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b
      (fun r hr => hjets r (by omega))
  obtain ⟨hfirst, hsecond⟩ :=
    DeepHorn.tendsto_scalarCurvature_derivatives_of_four_jets Dseq D b x hjets
  exact LeviCivitaData.tendsto_laplacian_of_metric_and_function_jets Dseq D x
    (fun i => contMDiffAt_iff_contDiffAt.mp ((Dseq i).contMDiff_scalarCurvature x))
    (contMDiffAt_iff_contDiffAt.mp (D.contMDiff_scalarCurvature x))
    hmetric hmetric' hfirst hsecond

def RiemannianMetric.scalarMetricFourJet
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (r : Fin 5) → Fin n → Fin n →
      ContinuousMultilinearMap ℝ (fun _ : Fin r.val => EuclideanSpace ℝ (Fin n)) ℝ :=
  fun r i j => iteratedFDeriv ℝ r.val (fun y => g.inner y (b i) (b j)) x

theorem LeviCivitaData.exists_scalar_laplacian_control_of_metric_fourJet
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) {α : ℝ} (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D' : LeviCivitaData h),
      (∀ r : ℕ, r ≤ 4 → ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ r (fun y => h.inner y (b i) (b j)) x -
          iteratedFDeriv ℝ r (fun y => g.inner y (b i) (b j)) x‖ < δ) →
      |D'.laplacian D'.scalarCurvature x - D.laplacian D.scalarCurvature x| < α := by
  classical
  let Data := (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) × LeviCivitaData h
  let J := fun p : Data => p.1.scalarMetricFourJet x b
  let L := Filter.comap J (𝓝 (g.scalarMetricFourJet x b))
  have hJ : Tendsto J L (𝓝 (g.scalarMetricFourJet x b)) := tendsto_comap
  have hjets (r : ℕ) (hr : r ≤ 4) (i j : Fin n) :
      Tendsto (fun p : Data => iteratedFDeriv ℝ r
        (fun y => p.1.inner y (b i) (b j)) x) L
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b i) (b j)) x)) := by
    let k : Fin 5 := ⟨r, by omega⟩
    exact ((continuous_apply j).tendsto _).comp
      (((continuous_apply i).tendsto _).comp
        (((continuous_apply k).tendsto _).comp hJ))
  have hF := LeviCivitaData.tendsto_scalar_laplacian_of_four_jets
    (fun p : Data => p.2) D b x hjets
  obtain ⟨δ, hδ, hbound⟩ := (Metric.nhds_basis_ball.comap J).mem_iff.mp
    (hF (Metric.ball_mem_nhds (D.laplacian D.scalarCurvature x) hα))
  refine ⟨δ, hδ, ?_⟩
  intro h D' hj
  have hclose : J ⟨h, D'⟩ ∈ Metric.ball (g.scalarMetricFourJet x b) δ := by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro r
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [dist_pi_lt_iff hδ]
    intro j
    simpa only [dist_eq_norm, J, RiemannianMetric.scalarMetricFourJet] using
      hj r.val (by omega) i j
  simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using hbound hclose

end PoincareConjecture
