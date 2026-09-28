import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Weak.Integral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Weak.Subharmonic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Weak.Harmonic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.LowDimension











noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric



theorem busemann_distributional_subharmonic
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M]
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, g.busemann γ x * D.laplacian φ x ∂g.volumeMeasure :=
  g.busemann_distributional_subharmonic_of_distance_comparison D hγ
    (D.integral_distance_mul_laplacian_le hm hcomplete hRic) φ hφ hc hφ0



theorem busemann_minimizing_line
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    (∀ x : M, Tendsto (fun t => g.busemannApprox γ t x) atTop
      (𝓝 (g.busemann γ x))) ∧
    (∀ x : M, Tendsto (fun t => g.busemannApprox (fun s => γ (-s)) t x) atTop
      (𝓝 (g.busemann (fun s => γ (-s)) x))) ∧
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann (fun s => γ (-s))) ∧
    (∀ x : M, g.busemann (fun s => γ (-s)) x = -g.busemann γ x) ∧
    (∀ s : ℝ, g.busemann γ (γ s) = s) ∧
    (∀ x : M, D.laplacian (g.busemann γ) x = 0) ∧
    (∀ x : M, g.inner x (D.gradient (g.busemann γ) x)
      (D.gradient (g.busemann γ) x) = 1) ∧
    (∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      D.hessian (g.busemann γ) x v w = 0) := by
  cases n with
  | zero => exact (g.not_minimizing_line_dim_zero γ hγ).elim
  | succ m =>
    cases m with
    | zero =>
      obtain ⟨hs, hr, hn, hh, hu, hess⟩ := g.busemann_properties_dim_one D hcomplete hγ
      have heq : g.busemann (fun t => γ (-t)) = fun x => -g.busemann γ x := funext hr
      refine ⟨g.tendsto_busemannApprox hγ,
        g.tendsto_busemannApprox (g.minimizing_line_reverse hγ), hs, ?_,
        hr, hn, hh, hu, hess⟩
      rw [heq]
      exact hs.neg
    | succ k =>
      let : MeasurableSpace M := borel M
      let : BorelSpace M := ⟨rfl⟩
      obtain ⟨hl, hlr, hs, hsr, hr, hn, hh, hu, _, hess⟩ :=
        g.busemann_properties_of_distributional_subharmonic D (by omega) hcomplete hRic hγ
          (g.busemann_distributional_subharmonic D (by omega) hcomplete hRic hγ)
          (g.busemann_distributional_subharmonic D (by omega) hcomplete hRic
            (g.minimizing_line_reverse hγ))
      exact ⟨hl, hlr, hs, hsr, hr, hn, hh, hu, hess⟩



theorem busemann_parallel_unit_gradient
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧
    (∀ x, g.inner x (D.gradient (g.busemann γ) x) (D.gradient (g.busemann γ) x) = 1) ∧
    (∀ x v, D.connection (D.gradient (g.busemann γ)) x v = 0) ∧
    (∀ x v w, D.hessian (g.busemann γ) x v w = 0) ∧
    g.busemann γ (γ 0) = 0 := by
  obtain ⟨_, _, hs, _, _, hn, hh, hu, hess⟩ :=
    g.busemann_minimizing_line D hcomplete hRic γ hγ
  exact ⟨hs, hu, g.busemann_connection_gradient_eq_zero D hcomplete hRic hγ hs hh,
    hess, hn 0⟩

end PoincareConjecture.RiemannianMetric
