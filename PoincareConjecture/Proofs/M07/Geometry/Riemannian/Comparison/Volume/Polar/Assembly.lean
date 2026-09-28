import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Density
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Domain
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Injectivity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace Poincare.VolumeComparison

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem volumeMeasure_ball_eq_polar_of_injOn
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hcut : g.volumeMeasure (e '' terminalRadialPoints
      (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0)
    (hinj : InjOn e
      (localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R)) :
    g.volumeMeasure (g.ball p r) =
      ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (n - 1)) *
          (localMinimizingSet (fun v => g.edist p (e v)) R \
            terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
            (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
            (t • (θ : EuclideanSpace ℝ (Fin n)))) ∂volume.toSphere := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hS : MeasurableSet S := by
    apply measurableSet_localMinimizingSet
    change ContinuousOn (fun v => EDist.edist p (e v)) (Metric.ball 0 R)
    exact continuous_edist.continuousOn.comp
      (continuous_const.continuousOn.prodMk he.continuousOn)
      (fun _ _ => Set.mem_univ _)
  have hball := volumeMeasure_ball_eq_image_sdiff_terminal
    g p hcover hcut hr hrR
  have hSD : MeasurableSet (S \ T) :=
    hS.diff (measurableSet_terminalRadialPoints hS)
  have hpolar := PoincareConjecture.RiemannianMetric.volumeMeasure_image_inter_ball_eq_polar
    g hn Metric.isOpen_ball he hSD (fun _ hx => hx.1.1) hinj r
  rw [hball]
  simpa only [S, T] using hpolar

theorem exists_precompact_polar_volume
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) (hn : 1 ≤ n) {R : ℝ}
    (hR : 0 < R) (hcompact : IsCompact (closure (g.ball p R))) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ e : EuclideanSpace ℝ (Fin n) → M,
        (∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) ∧
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧
        e 0 = p ∧
        HasFDerivAt (fun v => (extChartAt (𝓡 n) p) (e v))
          L.toContinuousLinearMap 0 ∧
        (∀ v ∈ Metric.ball 0 R,
          g.IsGeodesicOn (fun t : ℝ => e (t • v))
            {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            g.tangentNorm (e (t • v))
              (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
            g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) ∧
        g.volumeMeasure (e '' terminalRadialPoints
          (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0 ∧
        InjOn e (localMinimizingSet (fun v => g.edist p (e v)) R \
          terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) ∧
        ∀ r : ℝ, 0 < r → r ≤ R →
          g.volumeMeasure (g.ball p r) =
            ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (n - 1)) *
                (localMinimizingSet (fun v => g.edist p (e v)) R \
                  terminalRadialPoints
                    (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
                  (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
                  (t • (θ : EuclideanSpace ℝ (Fin n)))) ∂volume.toSphere := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hcut⟩ :=
    exists_precompact_polar_cut_null g p hR hcompact
  have hcover := image_localMinimizingSet_eq_ball
    g p hR hcompact L e hL he0 hed (fun v hv => (hgeo v hv).1)
  have hinj := injOn_localMinimizingSet_sdiff_terminal
    g p he0 hed (fun v hv => (hgeo v hv).1)
    (fun v hv => ((hgeo v hv).2 0 (by simp)).1)
  exact ⟨L, e, hL, he, he0, hed, hgeo, hcut, hinj,
    fun _ hr hrR => volumeMeasure_ball_eq_polar_of_injOn g p hn hr hrR he hcover hcut hinj⟩

end Poincare.VolumeComparison
