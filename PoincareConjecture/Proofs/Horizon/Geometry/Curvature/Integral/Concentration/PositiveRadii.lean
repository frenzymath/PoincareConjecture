import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.VariableRadii








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData



theorem integral_scalarCurvature_posPart_ball_le_integral_add_model_of_le_radius
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p : M) (hn : 1 ≤ n)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    {r R : ℝ} (hR : 0 ≤ R) (hrR : r ≤ R) :
    (∫ x in g.ball p r, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      (∫ x in g.ball p r, D.scalarCurvature x ∂g.volumeMeasure) +
        (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 R := by
  by_cases hr : 0 < r
  · exact (D.integral_scalarCurvature_posPart_ball_le_integral_add_model
      p hn hcomplete hsec hr).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (RiemannianMetric.modelVolume_mono_radius n zero_le_one hr.le hrR) (sq_nonneg _)))
  · let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
    let := g.toMetricSpace
    have he : g.ball p r = ∅ := by
      rw [← g.toMetricSpace_ball]
      exact Metric.ball_eq_empty.mpr (le_of_not_gt hr)
    rw [he, setIntegral_empty, setIntegral_empty, zero_add]
    exact mul_nonneg (sq_nonneg _) (RiemannianMetric.modelVolume_nonneg n zero_le_one hR)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture



theorem exists_subseq_prescribed_center_scalar_integral_tendsto_atTop_with_positive_radii
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι : Type*} [Fintype ι]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (q : ∀ j, ι → M j) (r : ℕ → ι → ℝ)
    (hn : 1 ≤ n) {R : ℝ} (hRpos : 0 < R) (hrR : ∀ j i, r j i ≤ R)
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (C : ℝ) (houtside : ∀ j,
      (∫ x in (g j).ball (p j) 1 \ ⋃ i, (g j).ball (q j i) (r j i),
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C)
    (hlarge : ∀ B : ℝ, ∃ j,
      B < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ j, 0 < r (phi j) i) ∧
      Tendsto (fun j => ∫ x in (g (phi j)).ball (q (phi j) i) (r (phi j) i),
        (D (phi j)).scalarCurvature x ∂(g (phi j)).volumeMeasure) atTop atTop := by
  have hR (j) : Continuous (D j).scalarCurvature := (D j).continuous_scalarCurvature
  have hP (j) : Continuous (fun x => max 0 ((D j).scalarCurvature x)) :=
    continuous_const.sup (hR j)
  have hPi (j) (x : M j) (s : ℝ) :=
    (g j).integrableOn_ball_of_continuous (hcomplete j) (hP j) x s
  have hRi (j) (x : M j) (s : ℝ) :=
    (g j).integrableOn_ball_of_continuous (hcomplete j) (hR j) x s
  have hm (j) (x : M j) (s : ℝ) : MeasurableSet ((g j).ball x s) := by
    let : MetricSpace (M j) := (g j).toMetricSpace
    rw [← (g j).toMetricSpace_ball]
    exact Metric.isOpen_ball.measurableSet
  have hlargeP : ∀ B : ℝ, ∃ j, B < ∫ x in (g j).ball (p j) 1,
      max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure := by
    intro B
    obtain ⟨j, hj⟩ := hlarge B
    exact ⟨j, hj.trans_le (integral_mono (hRi j _ _) (hPi j _ _)
      (fun x => le_max_right _ _))⟩
  obtain ⟨i, phi, hphi, hdiv⟩ :=
    Poincare.CurvatureIntegral.exists_subseq_fixed_member_integral_tendsto_atTop
      (fun j => (g j).volumeMeasure) (fun j => (g j).ball (p j) 1)
      (fun j i => (g j).ball (q j i) (r j i))
      (fun j x => max 0 ((D j).scalarCurvature x))
      (fun j => hm j _ _) (fun j i => hm j _ _) (fun j x => le_max_left _ _)
      (fun j => hPi j _ _) (fun j i => hPi j _ _) C houtside hlargeP
  have hbound (j : ℕ) :=
    (D j).integral_scalarCurvature_posPart_ball_le_integral_add_model_of_le_radius
      (q j i) hn (hcomplete j) (hsec j) hRpos.le (hrR j i)
  have hsigned : Tendsto (fun j => ∫ x in (g (phi j)).ball (q (phi j) i) (r (phi j) i),
      (D (phi j)).scalarCurvature x ∂(g (phi j)).volumeMeasure) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [(tendsto_atTop.1 hdiv)
      (B + (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 R)] with j hj
    linarith only [hj, hbound (phi j)]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsigned.eventually (eventually_gt_atTop 0))
  refine ⟨i, fun j => phi (j + J), fun a b hab => hphi (Nat.add_lt_add_right hab J),
    ?_, hsigned.comp (tendsto_add_atTop_nat J)⟩
  intro j
  by_contra! hr
  let : ConnectedSpace (M (phi (j + J))) := { toNonempty := ⟨p (phi (j + J))⟩ }
  let := (g (phi (j + J))).toMetricSpace
  have he : (g (phi (j + J))).ball (q (phi (j + J)) i) (r (phi (j + J)) i) = ∅ := by
    rw [← (g (phi (j + J))).toMetricSpace_ball]
    exact Metric.ball_eq_empty.mpr hr
  have hj := hJ (j + J) (by omega)
  rw [he, setIntegral_empty] at hj
  exact lt_irrefl _ hj

end PoincareConjecture
