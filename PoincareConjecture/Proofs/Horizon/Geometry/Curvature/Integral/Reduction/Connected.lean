import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Component


noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem metricComplete_connectedComponentMetric (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) :
    MetricComplete (g.connectedComponentMetric p) :=
  metricComplete_of_subtype_val isClosed_connectedComponent g _
    (fun _ _ _ => rfl) hcomplete

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem sectionalCurvature_connectedComponentMetric
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
    (v w : TangentSpace (𝓡 n) x) :
    (g.connectedComponentMetric p).leviCivitaData.sectionalCurvature x v w =
      D.sectionalCurvature x
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x v)
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x w) := by
  have hR := (g.connectedComponentMetric p).leviCivitaData.curvatureTensor_eq_of_local_isometry
    D isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x) v w v w
  unfold LeviCivitaData.sectionalCurvature
  rw [hR]
  rfl



theorem scalar_integral_le_of_connected_bound
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (C : ℝ)
    (hbound : ∀ (N : Type u) [TopologicalSpace N] [T3Space N]
      [MeasurableSpace N] [BorelSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
      [PreconnectedSpace N] (h : RiemannianMetric n N) (E : LeviCivitaData h),
      MetricComplete h →
      (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ E.sectionalCurvature x v w) →
      ∀ q, (∫ x in h.ball q 1, E.scalarCurvature x ∂h.volumeMeasure) ≤ C)
    (p : M) :
    (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let gU := g.connectedComponentMetric p
  have hsecU (x : U) (v w : TangentSpace (𝓡 n) x) :
      -1 ≤ gU.leviCivitaData.sectionalCurvature x v w := by
    rw [sectionalCurvature_connectedComponentMetric]
    exact hsec _ _ _
  have h := hbound U gU gU.leviCivitaData
    (g.metricComplete_connectedComponentMetric hcomplete p) hsecU
    ⟨p, mem_connectedComponent⟩
  rw [← g.integral_scalarCurvature_ball_connectedComponent D p 1]
  exact h

end PoincareConjecture.RiemannianMetric
