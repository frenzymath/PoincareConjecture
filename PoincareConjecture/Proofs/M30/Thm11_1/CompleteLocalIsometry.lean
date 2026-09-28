import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Geodesic.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M30




theorem surjective_of_complete_pullback_eq
    {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [T3Space M] [TopologicalSpace N] [T3Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    [Nonempty M] [PreconnectedSpace N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (hg : MetricComplete g) (hh : MetricComplete h)
    (f : M → N) (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hmetric : ∀ x, ∀ a b : TangentSpace (𝓡 n) x,
      h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x a)
        (mfderiv (𝓡 n) (𝓡 n) f x b) = g.inner x a b) :
    Function.Surjective f := by
  classical
  let p : M := Classical.choice inferInstance
  intro y
  obtain ⟨ε, hε, η, hη, hη0, hη1, _⟩ :=
    h.exists_minimizing_geodesic_of_metricComplete hh (f p) y
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  let w := deriv (fun t => extChartAt (𝓡 n) (f p) (η t)) 0
  have hηv : HasDerivAt (fun t => extChartAt (𝓡 n) (f p) (η t)) w 0 :=
    (hη.hasDerivAt_chart_at h0 (f p) (by
      rw [hη0]
      exact mem_extChartAt_source (f p))).1
  obtain ⟨v, hv⟩ := (g.mfderiv_bijective_of_pullback_eq h p (hmetric p)).2 w
  obtain ⟨γ, hγ, hγ0, hcoord⟩ := g.exists_global_geodesic hg p v
  have hs := RiemannianMetric.contMDiff_global_geodesic hγ
  have hinit : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = v := by
    have hp : γ 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
      rw [hγ0]
      exact mem_chart_source _ p
    have heq := congrArg (fun L => L 1) (mfderiv_comp 0
      ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hp).mdifferentiableAt (by simp))
      ((hs 0).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0 =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at heq
    rw [hcoord.deriv, hγ0, mfderiv_extChartAt_self] at heq
    exact heq.symm
  have hθ : h.IsGeodesicOn (f ∘ γ) univ :=
    RiemannianMetric.IsGeodesicOn.comp_local_isometry_manifold isOpen_univ
      hf.contMDiffOn (fun x _ a b => (hmetric x a b).symm) hγ
      (fun _ _ => mem_univ _)
  have hθ0 : (f ∘ γ) 0 = f p := by simp only [Function.comp_apply, hγ0]
  have hθinit : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ γ) 0 1 = w := by
    have heq := mfderiv_comp_apply 0 ((hf _).mdifferentiableAt (by simp))
      ((hs 0).mdifferentiableAt (by simp)) (1 : ℝ)
    rw [hinit, hγ0, hv] at heq
    exact heq
  have hθv := (hθ.hasDerivAt_chart_at (mem_univ 0) (f p) (by
    rw [hθ0]
    exact mem_extChartAt_source (f p))).1
  have hθs := RiemannianMetric.contMDiff_global_geodesic hθ
  have hchart : (f ∘ γ) 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (f p)).source := by
    rw [hθ0]
    exact mem_chart_source _ (f p)
  have heq := congrArg (fun L => L 1) (mfderiv_comp 0
    ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hchart).mdifferentiableAt (by simp))
    ((hθs 0).mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun t => extChartAt (𝓡 n) (f p) ((f ∘ γ) t)) 0 =
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (f p)) ((f ∘ γ) 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ γ) 0 1) at heq
  rw [hθ0, mfderiv_extChartAt_self] at heq
  change deriv (fun t => extChartAt (𝓡 n) (f p) ((f ∘ γ) t)) 0 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ γ) 0 1 at heq
  rw [heq, hθinit] at hθv
  have hend := RiemannianMetric.geodesic_endpoint_eq_of_initial_data
    (fun t _ => hθ t (mem_univ t))
    (fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
      hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    hθ0 hη0 hθv hηv
  exact ⟨γ 1, hend.trans hη1⟩

end PoincareConjecture.M30
