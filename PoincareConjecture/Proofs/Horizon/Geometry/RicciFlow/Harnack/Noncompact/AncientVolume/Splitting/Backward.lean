import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.Persistence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RicciFlow



theorem ancient_backward_persistence_of_parallel_gradient
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hn : 1 ≤ n)
    (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hcurv : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ≤ 0, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : RiemannianMetric.HasUnitGradient (F.connection 0) f)
    (hzero : RiemannianMetric.HasZeroHessian (F.connection 0) f) :
    ∀ t ≤ 0, (F.connection t).gradient f = (F.connection 0).gradient f ∧
      RiemannianMetric.HasUnitGradient (F.connection t) f ∧
      RiemannianMetric.HasZeroHessian (F.connection t) f := by
  intro t ht
  rcases lt_or_eq_of_le ht with ht | rfl
  · have hsub : Icc t 0 ⊆ Iic 0 := fun _ hs => hs.2
    let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub ordConnected_Icc
      ⟨t, left_mem_Icc.mpr ht.le, 0, right_mem_Icc.mpr ht.le, ht.ne⟩
    have hGbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc t 0, ∀ x,
        (G.connection s).curvatureTensorNorm x ≤ K := by
      obtain ⟨K, hK, hb⟩ := hbound
      exact ⟨K, hK, fun s hs x => hb s hs.2 x⟩
    exact Splitting.backward_persistence_of_parallel_gradient hC hn ht G
      (fun s hs => hcomplete s hs.2) (fun s hs => hcurv s hs.2)
      hGbound f hf hunit hzero t ⟨le_rfl, ht.le⟩
  · exact ⟨rfl, hunit, hzero⟩

end PoincareConjecture.RicciFlow
