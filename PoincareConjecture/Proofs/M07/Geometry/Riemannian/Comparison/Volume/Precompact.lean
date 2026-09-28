import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.BallCoverage
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.CenterDensity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.IntegralRatio
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.ModelIntegral
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Riccati
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Matrix
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Density
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Root
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Cutoff
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.OneDimensional
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.CutoffComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Assembly















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem volumeMeasure_ball_lt_top_of_precompact
    (g : RiemannianMetric n M) (p : M) {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    g.volumeMeasure (g.ball p r) < ⊤ := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  calc
    g.volumeMeasure (g.ball p r) ≤
        g.volumeMeasure {q | g.edist p q ≤ ENNReal.ofReal r} := by
      apply measure_mono
      intro q hq
      change g.edist p q < ENNReal.ofReal r at hq
      exact le_of_lt hq
    _ < ⊤ := g.volumeMeasure_lt_top_of_isCompact
      (g.isCompact_closedBall_of_precompact_ball p hR hrR hcompact)






theorem relativeVolumeComparison_of_precompact_ball
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n) {R κ : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ)
    (hcompact : IsCompact (closure (g.ball p R)))
    (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤
        D.ricci x v v) :
    AntitoneOn
      (fun r : ℝ =>
        g.volumeMeasure (g.ball p r) /
          ENNReal.ofReal (modelVolume n κ r))
      (Ioo 0 R) ∧
      Tendsto
        (fun r : ℝ =>
          g.volumeMeasure (g.ball p r) /
            ENNReal.ofReal (modelVolume n κ r))
        (𝓝[>] 0) (𝓝 1) := by
  refine ⟨?_, g.tendsto_volumeMeasure_ball_div_modelVolume p hn hκ⟩
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hcut, hinj, hvolume⟩ :=
    Poincare.VolumeComparison.exists_precompact_polar_volume g p hn hR hcompact
  let S := Poincare.VolumeComparison.localMinimizingSet (fun v => g.edist p (e v)) R
  let T := Poincare.VolumeComparison.terminalRadialPoints S R
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hS : MeasurableSet S := by
    apply Poincare.VolumeComparison.measurableSet_localMinimizingSet
    change ContinuousOn (fun v => EDist.edist p (e v)) (Metric.ball 0 R)
    exact continuous_edist.continuousOn.comp
      (continuous_const.continuousOn.prodMk he.continuousOn)
      (fun _ _ => Set.mem_univ _)
  have hT : MeasurableSet T := by
    exact Poincare.VolumeComparison.measurableSet_terminalRadialPoints (R := R) hS
  have hST : MeasurableSet (S \ T) := hS.diff hT
  have hρ := g.measurable_indicator_pullbackVolumeDensity (s := S \ T)
    Metric.isOpen_ball he hST (fun _ hx => hx.1.1)
  let F : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ → ℝ≥0∞ :=
    fun θ t => ENNReal.ofReal (t ^ (n - 1)) *
      (S \ T).indicator (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
        (t • (θ : EuclideanSpace ℝ (Fin n)))
  have hF : Measurable (fun q : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ =>
      F q.1 q.2) :=
    (ENNReal.continuous_ofReal.comp (continuous_snd.pow (n - 1))).measurable.mul
      (hρ.comp (continuous_snd.smul
        (continuous_subtype_val.comp continuous_fst)).measurable)
  have hcross : ∀ θ, ∀ t ∈ Ioo (0 : ℝ) R, ∀ s ∈ Ioo (0 : ℝ) R,
      t ≤ s → F θ s * ENNReal.ofReal (modelS κ t ^ (n - 1)) ≤
        F θ t * ENNReal.ofReal (modelS κ s ^ (n - 1)) := by
    intro θ t ht s hs hts
    exact g.radialDensity_cross_le D hn hR hκ hL he he0 hed hgeo hRic θ ht hs hts
  have hm := antitoneOn_angular_div_modelVolume volume.toSphere hn hκ hF hcross
  intro r hr s hs hrs
  dsimp only
  rw [hvolume r hr.1 hr.2.le, hvolume s hs.1 hs.2.le]
  exact hm hr hs hrs


theorem smallBall_volume_lower_bound_of_precompact_ball
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n) {R κ r s : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ)
    (hcompact : IsCompact (closure (g.ball p R)))
    (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    (hr : 0 < r) (hrs : r ≤ s) (hsR : s < R) :
    (ENNReal.ofReal (modelVolume n κ r) / ENNReal.ofReal (modelVolume n κ s)) *
      g.volumeMeasure (g.ball p s) ≤ g.volumeMeasure (g.ball p r) := by
  have hm := (g.relativeVolumeComparison_of_precompact_ball p hn hR hκ hcompact D hRic).1
    ⟨hr, hrs.trans_lt hsR⟩ ⟨hr.trans_le hrs, hsR⟩ hrs
  have hr0 : ENNReal.ofReal (modelVolume n κ r) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (modelVolume_pos hn hκ hr)).ne'
  have hmul := mul_le_mul' hm (le_refl (ENNReal.ofReal (modelVolume n κ r)))
  rw [ENNReal.div_mul_cancel hr0 ENNReal.ofReal_ne_top] at hmul
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

end PoincareConjecture.RiemannianMetric
