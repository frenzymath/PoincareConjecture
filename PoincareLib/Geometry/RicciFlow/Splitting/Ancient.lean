import PoincareLib.Geometry.RicciFlow.Splitting.Persistence

/-!
# Parallel gradients on ancient Ricci flows

Closed-slab persistence preserves a terminal unit parallel gradient at every
earlier time of an ancient flow, with the same function and vector field.
This supplies the persistence hypotheses of the fixed-factor construction.

Reference: Kleiner--Lott (corrected 2013), Proposition 41.13, p. 2678.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RicciFlow.Splitting

/-- Terminal unit parallel gradients persist on the whole ancient interval. -/
theorem ancient_parallel_gradient
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hn : 1 ≤ n) {b : ℝ}
    (F : RicciFlow n M (Iic b))
    (hc : ∀ t ≤ b, MetricComplete (F.metric t))
    (hop : ∀ t ≤ b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ≤ b, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hu : RiemannianMetric.HasUnitGradient (F.connection b) f)
    (hz : RiemannianMetric.HasZeroHessian (F.connection b) f) :
    ∀ t ≤ b, (F.connection t).gradient f = (F.connection b).gradient f ∧
      RiemannianMetric.HasUnitGradient (F.connection t) f ∧
      RiemannianMetric.HasZeroHessian (F.connection t) f := by
  intro t ht
  have hab : t - 1 < b := by linarith
  have hsub : Icc (t - 1) b ⊆ Iic b := fun _ hs => hs.2
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub ordConnected_Icc
    ⟨t - 1, left_mem_Icc.mpr hab.le, b, right_mem_Icc.mpr hab.le, hab.ne⟩
  obtain ⟨K, hK, hnorm⟩ := hbound
  exact backward_persistence_of_parallel_gradient hC hn hab G
    (fun s hs => hc s hs.2) (fun s hs => hop s hs.2)
    ⟨K, hK, fun s hs => hnorm s hs.2⟩ f hf hu hz t ⟨by linarith, ht⟩

end PoincareMT.RicciFlow.Splitting
