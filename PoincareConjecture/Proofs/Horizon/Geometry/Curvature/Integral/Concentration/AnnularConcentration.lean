import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.ScalarAnnuli

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

theorem integral_scalarCurvature_posPart_outside_iUnion_ball_le_of_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {ι : Type*} [Fintype ι] (q : ι → M) (a r₀ R C : ι → ℝ) {m : ℕ}
    (ha : ∀ i, 0 ≤ a i) (hr₀ : ∀ i, 0 < r₀ i)
    (hR : ∀ i, R i < 19 * r₀ i / 16) (hC : ∀ i, 0 ≤ C i) (hm : 1 ≤ m)
    (hcover : g.ball p 1 ⊆ ⋃ i, g.ball (q i) (R i))
    (hbound : ∀ i, ∀ r : ℝ, 0 < r → 2 * a i ≤ r → r ≤ r₀ i →
      (∫ x in {x : M | (g.edist (q i) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C i * r ^ m) :
    (∫ x in g.ball p 1 \ ⋃ i, g.ball (q i) (4 * a i),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        ∑ i, C i * r₀ i ^ m / (1 - (227 / 228 : ℝ) ^ m) := by
  classical
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let := g.toMetricSpace
  let E := g.ball p 1 \ ⋃ i, g.ball (q i) (4 * a i)
  let B := fun i => g.ball (q i) (R i) \ g.ball (q i) (4 * a i)
  let h : M → ℝ := fun x => max 0 (D.scalarCurvature x)
  have hmeas (x : M) (r : ℝ) : MeasurableSet (g.ball x r) := by
    rw [← g.toMetricSpace_ball]
    exact Metric.isOpen_ball.measurableSet
  have hcont : Continuous h := continuous_const.max D.continuous_scalarCurvature
  have hEm : MeasurableSet E := (hmeas p 1).diff
    (MeasurableSet.iUnion (fun i => hmeas (q i) (4 * a i)))
  have hBm (i : ι) : MeasurableSet (B i) :=
    (hmeas (q i) (R i)).diff (hmeas (q i) (4 * a i))
  have hEi : IntegrableOn h E g.volumeMeasure :=
    (g.integrableOn_ball_of_continuous hcomplete hcont p 1).mono_set sdiff_subset
  have hBi (i : ι) : IntegrableOn h (B i) g.volumeMeasure :=
    (g.integrableOn_ball_of_continuous hcomplete hcont (q i) (R i)).mono_set sdiff_subset
  have hEB : E ⊆ ⋃ i ∈ (Finset.univ : Finset ι), B i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.1)
    refine mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi, ?_⟩
    exact fun hb => hx.2 (mem_iUnion.mpr ⟨i, hb⟩)
  apply (Poincare.CurvatureIntegral.integral_le_sum_of_finset_cover hEm
    Finset.univ B (fun i _ => hBm i) (fun _ => le_max_left _ _) hEi
    (fun i _ => hBi i) hEB).trans
  exact Finset.sum_le_sum (fun i _ =>
    D.integral_scalarCurvature_posPart_outside_ball_le_of_nonneg_scale_annuli
      hn hcomplete (q i) (ha i) (hr₀ i) (hR i) (hC i) hm (hbound i))

end PoincareConjecture.LeviCivitaData
