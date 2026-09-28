import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.UmbilicRigidity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.FiniteRatio

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

theorem infinite_scalar_ratio_of_bounded_ancient
    {n : ℕ} (hn : 2 ≤ n) {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ x : M, 0 < (F.connection 0).scalarCurvature x)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r)) :
    ∀ t₀ ≤ 0, ∀ p : M, ∀ L A : ℝ, ∃ x : M,
      L < ((F.metric t₀).edist p x).toReal ∧
      A < (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro t₀ ht₀ p
  by_contra hfinite
  have hdecay := F.quadratic_decay_of_finite_scalar_ratio hC hcomplete hoperator
    hK hbound hnonflat hκ hnoncollapse (by omega) t₀ ht₀ p hfinite
  have hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C := by
    intro C hCpos
    obtain ⟨L, _, hL⟩ := hdecay C hCpos
    exact ⟨L, hL⟩
  have hflat := F.curvature_eq_zero_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  have hpositive := F.scalarCurvature_pos_of_bounded_ancient hC hcomplete hoperator
    hK hbound hnonflat t₀ ht₀ p
  rw [(hflat p).1] at hpositive
  exact lt_irrefl _ hpositive

end PoincareConjecture.RicciFlow
