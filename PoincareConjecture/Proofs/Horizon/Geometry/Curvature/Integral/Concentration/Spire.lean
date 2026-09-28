import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.NestedCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

theorem exists_subseq_prescribed_center_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι : Type*} [Fintype ι]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (q : ∀ j, ι → M j) (r : ι → ℝ)
    (hn : 1 ≤ n) (hr : ∀ i, 0 < r i)
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (C : ℝ) (houtside : ∀ j,
      (∫ x in (g j).ball (p j) 1 \ ⋃ i, (g j).ball (q j i) (r i),
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C)
    (hlarge : ∀ B : ℝ, ∃ j,
      B < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun j => ∫ x in (g (phi j)).ball (q (phi j) i) (r i),
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
      (fun j i => (g j).ball (q j i) (r i))
      (fun j x => max 0 ((D j).scalarCurvature x))
      (fun j => hm j _ _) (fun j i => hm j _ _) (fun j x => le_max_left _ _)
      (fun j => hPi j _ _) (fun j i => hPi j _ _) C houtside hlargeP
  have hbound (j : ℕ) :
      (∫ x in (g j).ball (q j i) (r i), max 0 ((D j).scalarCurvature x)
        ∂(g j).volumeMeasure) ≤
      (∫ x in (g j).ball (q j i) (r i), (D j).scalarCurvature x
        ∂(g j).volumeMeasure) + (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 (r i) :=
    (D j).integral_scalarCurvature_posPart_ball_le_integral_add_model
      (q j i) hn (hcomplete j) (hsec j) (hr i)
  refine ⟨i, phi, hphi, tendsto_atTop.2 (fun B => ?_)⟩
  filter_upwards [(tendsto_atTop.1 hdiv)
    (B + (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 (r i))] with j hj
  linarith only [hj, hbound (phi j)]

theorem exists_subseq_prescribed_center_scalar_integral_tendsto_atTop_at_scales
    {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι : Type*} [Fintype ι]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (p : ∀ j, M j) (q : ∀ j, ι → M j) (r : ℕ → ι → ℝ)
    (hn : 1 ≤ n) (hr : ∀ k i, 0 < r k i) (hranti : ∀ i, Antitone (fun k => r k i))
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (C : ℕ → ℝ) (houtside : ∀ k j,
      (∫ x in (g j).ball (p j) 1 \ ⋃ i, (g j).ball (q j i) (r k i),
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ C k)
    (hlarge : ∀ B : ℝ, ∃ j,
      B < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (scale : ℕ → ℕ) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun j => ∫ x in (g (phi j)).ball (q (phi j) i) (r (scale j) i),
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
  have hnested (j : ℕ) (i : ι) : Antitone (fun k => (g j).ball (q j i) (r k i)) := by
    intro k l hkl x hx
    exact lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (hranti i hkl))
  obtain ⟨i, hi⟩ := Poincare.CurvatureIntegral.exists_fixed_member_integral_unbounded_all_scales
    (fun j => (g j).volumeMeasure) (fun j => (g j).ball (p j) 1)
    (fun j k i => (g j).ball (q j i) (r k i))
    (fun j x => max 0 ((D j).scalarCurvature x))
    (fun j => hm j _ _) (fun j k i => hm j _ _) (fun j x => le_max_left _ _)
    (fun j => hPi j _ _) (fun j k i => hPi j _ _) hnested C houtside hlargeP
  obtain ⟨phi, hphi, hvalue⟩ := Poincare.CurvatureIntegral.exists_strictMono_above_thresholds_family
    (fun k j => ∫ x in (g j).ball (q j i) (r (scale k) i),
      max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure)
    (fun k => (k : ℝ) + (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 (r (scale k) i))
    (fun k => hi (scale k))
  refine ⟨i, phi, hphi, tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop⟩
  have hb := (D (phi j)).integral_scalarCurvature_posPart_ball_le_integral_add_model
    (q (phi j) i) hn (hcomplete (phi j)) (hsec (phi j)) (hr (scale j) i)
  linarith only [hvalue j, hb]

end PoincareConjecture
