import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.DensityBound
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.FiniteFibers
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Coverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_finite_fiber_on_ball_of_center_fiber
    (g : RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (he0 : e 0 = p)
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖)
    (hcover : e '' Poincare.VolumeComparison.localMinimizingSet
      (fun v => g.edist p (e v)) R = g.ball p R)
    {k : ℕ} (y : Fin k → EuclideanSpace ℝ (Fin n)) (hy : Injective y)
    (hyp : ∀ i, e (y i) = p) (hshort : ∀ i, ‖y i‖ + 2 * r < R) :
    ∀ q ∈ g.ball p r, ∃ z : Fin k → EuclideanSpace ℝ (Fin n),
      Injective z ∧ ∀ i, z i ∈ Metric.ball 0 R ∧ e (z i) = q := by
  intro q hq
  rw [← Poincare.VolumeComparison.image_localMinimizingSet_inter_ball
    g p hcover hr hrR] at hq
  obtain ⟨v, ⟨hv, hvr⟩, hvq⟩ := hq
  have htmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt
      (by simpa using hv.1)
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun u : ℝ => e (u • v)) t :=
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (htmem t ht))).comp t
      (contMDiffAt_iff_contDiffAt.mpr (by fun_prop))
  obtain ⟨z, hz, hzp⟩ := exists_finite_fiber_at_curve_endpoint g he hbij hlower
    hc (norm_nonneg v) (fun t ht => (hspeed v hv.1 t ht).le) y hy
    (fun i => by simpa only [zero_smul, he0] using hyp i) (fun i => by
      have hvlt : ‖v‖ < r := by simpa using hvr
      linarith [hshort i])
  exact ⟨z, hz, fun i => ⟨(hzp i).1, by simpa only [one_smul, hvq] using (hzp i).2.1⟩⟩

theorem mul_volumeMeasure_ball_le_of_center_fiber
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric n M) (p : M) {R r : ℝ}
    (hR : 0 < R) (hcompact : IsCompact (closure (g.ball p R)))
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖)
    (hb : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x w) ∧
      g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x w) ≤ 3 * ‖w‖ / 2)
    (hr : 0 < r) (hrR : r ≤ R)
    {k : ℕ} (y : Fin k → EuclideanSpace ℝ (Fin n)) (hy : Injective y)
    (hyp : ∀ i, e (y i) = p) (hshort : ∀ i, ‖y i‖ + 2 * r < R) :
    (k : ℝ≥0∞) * g.volumeMeasure (g.ball p r) ≤
      ENNReal.ofReal ((n.factorial : ℝ) * (3 / 2 : ℝ) ^ n) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
  have hbij (x) (hx : x ∈ Metric.ball 0 R) :=
    g.bijective_mfderiv_of_tangentNorm_lower_bound x (fun w => (hb x hx w).1)
  have hcover := Poincare.VolumeComparison.image_localMinimizingSet_eq_ball
    g p hR hcompact L e hL he0 hed hgeo
  have hfib := g.exists_finite_fiber_on_ball_of_center_fiber p hr hrR he he0 hbij
    (fun x hx w => (hb x hx w).1) hspeed hcover y hy hyp hshort
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hmeas : MeasurableSet (g.ball p r) := by
    change MeasurableSet {q : M | EDist.edist p q < ENNReal.ofReal r}
    simp_rw [edist_comm p]
    exact Metric.isOpen_eball.measurableSet
  apply g.mul_volumeMeasure_le_of_differential_bound_of_finite_fibers
    Metric.isOpen_ball hmeas he hbij _ hfib
  intro x hx w
  convert (hb x hx w).2 using 1
  ring

end PoincareConjecture.RiemannianMetric
