import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Monotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.PointSelection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureTensorNorm_le_of_bounded_ancient_terminal_scalar
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {t : ℝ} (ht : t ≤ 0) {S : Set M} {A : ℝ}
    (hscalar : ∀ x ∈ S, (F.connection t).scalarCurvature x ≤ A) :
    ∀ s ≤ t, ∀ x ∈ S, (F.connection s).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * A := by
  intro s hs x hx
  have hs0 := hs.trans ht
  apply ((F.connection s).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus n M (F.metric s) (F.connection s)) x (hoperator s hs0 x)).trans
  exact mul_le_mul_of_nonneg_left
    (((F.scalarCurvature_monotoneOn_of_bounded_ancient hC hcomplete hoperator hK hbound x)
      hs0 ht hs).trans (hscalar x hx)) (sq_nonneg _)

theorem exists_escaping_backward_curvature_controlled_sequence
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {t : ℝ} (ht : t ≤ 0) (p : M)
    (hunbounded : ¬ BddAbove (range (fun x =>
      ((F.metric t).edist p x).toReal ^ 2 * (F.connection t).scalarCurvature x))) :
    ∃ q : ℕ → M, ∃ r : ℕ → ℝ,
      (∀ i, 0 < (F.connection t).scalarCurvature (q i) ∧ 0 < r i ∧
        (∀ y ∈ (F.metric t).ball (q i) (r i),
          (F.connection t).scalarCurvature y ≤ 4 * (F.connection t).scalarCurvature (q i)) ∧
        ∀ s ≤ t, ∀ y ∈ (F.metric t).ball (q i) (r i),
          (F.connection s).curvatureTensorNorm y ≤
            4 * (n : ℝ) ^ 2 * (F.connection t).scalarCurvature (q i)) ∧
      Tendsto (fun i => ((F.metric t).edist p (q i)).toReal) atTop atTop ∧
      Tendsto r atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt ((F.connection t).scalarCurvature (q i))) atTop atTop ∧
      Tendsto (fun i => ((F.metric t).edist p (q i)).toReal *
        Real.sqrt ((F.connection t).scalarCurvature (q i))) atTop atTop ∧
      Tendsto (fun i => r i / ((F.metric t).edist p (q i)).toReal) atTop (𝓝 0) ∧
      BddAbove (range (fun i => (F.connection t).scalarCurvature (q i))) := by
  have hscalar (x : M) : 0 ≤ (F.connection t).scalarCurvature x :=
    ((F.connection t).curvatureOperatorBound_scalarCurvature
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (hoperator t ht x)).1
  have hbounded : BddAbove (range (F.connection t).scalarCurvature) := by
    refine ⟨(n : ℝ) ^ 2 * K, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (((F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
      (mul_le_mul_of_nonneg_left (hbound t ht x) (sq_nonneg _)))
  obtain ⟨q, r, hcontrol, hlimits⟩ :=
    (F.metric t).exists_escaping_curvature_controlled_sequence
      (F.connection t).scalarCurvature hscalar hbounded p hunbounded
  refine ⟨q, r, ?_, hlimits⟩
  intro i
  refine ⟨(hcontrol i).1, (hcontrol i).2.1, (hcontrol i).2.2, ?_⟩
  simpa only [mul_left_comm, mul_assoc] using
    F.curvatureTensorNorm_le_of_bounded_ancient_terminal_scalar hC hcomplete hoperator hK hbound
      ht (hcontrol i).2.2

theorem ball_volume_lower_bound_of_bounded_ancient_terminal_scalar
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ}
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    {t : ℝ} (ht : t ≤ 0) (x : M) {r A : ℝ} (hr : 0 < r)
    (hscalar : ∀ y ∈ (F.metric t).ball x r, (F.connection t).scalarCurvature y ≤ A)
    (hscale : (n : ℝ) ^ 2 * A ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r) := by
  apply hnoncollapse t ht x r hr
  intro s hs y hy
  exact (F.curvatureTensorNorm_le_of_bounded_ancient_terminal_scalar
    hC hcomplete hoperator hK hbound ht hscalar s hs.2 y hy).trans hscale

end PoincareConjecture.RicciFlow
