import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Ball
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.GaussianSummation

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

theorem integrable_gaussian_heat_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {A b V c a : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hV : 0 ≤ V) (ha : 0 < a)
    (hbound : ∀ t ∈ Icc 0 b, ∀ x, |F (t, x)| ≤ (g.edist O x).toReal + A)
    (hvol : ∀ R : ℝ, 1 ≤ R →
      (g.volumeMeasure {x | (g.edist O x).toReal ≤ R}).toReal ≤ V * Real.exp (c * R)) :
    Integrable (fun p : ℝ × M ↦ Real.exp (-a * (g.edist O p.2).toReal ^ 2) *
      g.inner p.2 (D.gradient (fun y ↦ F (p.1, y)) p.2)
        (D.gradient (fun y ↦ F (p.1, y)) p.2))
      ((volume.restrict (Ioc 0 b)).prod g.volumeMeasure) := by
  refine Poincare.Analysis.Heat.integrable_gaussian_weight_of_ball_integral_le_exp
    ((g.continuous_toReal_edist O).comp continuous_snd).measurable
    (D.aestronglyMeasurable_heat_gradient_normSq hF hheat measurableSet_Ioc
      (fun _ ht ↦ ht.1) volume) (fun _ ↦ ENNReal.toReal_nonneg) ?_ ha
    (fun j ↦ D.integrable_heat_energy_on_ball hcomplete O hF hFc hheat hb
      (by linarith [Nat.cast_nonneg j (α := ℝ)] : 1 ≤ (j : ℝ) + 1))
    (C := (5 + A) ^ 2 * (1 + 4 * b * heatCutoffConstant ^ 2) * V)
    (c := 2 + 5 * c) ?_
  · intro p
    by_cases hv : D.gradient (fun y ↦ F (p.1, y)) p.2 = 0
    · simp [hv]
    · exact (g.pos p.2 _ hv).le
  · intro j
    have hR : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg j (α := ℝ)]
    have hlocal := D.integral_heat_energy_on_ball_le hcomplete O hF hFc hheat
      hA hb hR hbound
    refine hlocal.trans ?_
    calc
      _ ≤ (5 * ((j : ℝ) + 1) + A) ^ 2 *
          (1 + 4 * b * (heatCutoffConstant / ((j : ℝ) + 1)) ^ 2) *
          (V * Real.exp (c * (5 * ((j : ℝ) + 1)))) := by
        exact mul_le_mul_of_nonneg_left (hvol _ (by linarith)) (by positivity)
      _ = (5 * ((j : ℝ) + 1) + A) ^ 2 *
          (1 + 4 * b * (heatCutoffConstant / ((j : ℝ) + 1)) ^ 2) * V *
          Real.exp (c * (5 * ((j : ℝ) + 1))) := by ring
      _ ≤ _ := Poincare.Analysis.Heat.cutoff_energy_growth_le_exp
        hR hA hb.le heatCutoffConstant_pos.le hV

end PoincareConjecture.LeviCivitaData
