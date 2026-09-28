import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.CutTime
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.GeodesicLength

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Manifold ContDiff Bundle

namespace Poincare.VolumeComparison

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem radial_mem_ball_of_mem_ball
    {R : ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
  rw [Metric.mem_ball, dist_zero_right] at hv ⊢
  rw [norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hv)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem radial_subsegment_upper
    (g : PoincareConjecture.RiemannianMetric n M)
    {R : ℝ} {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball 0 R)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    g.edist (e (a • v)) (e v) ≤
    ENNReal.ofReal ‖v‖ * ENNReal.ofReal (1 - a) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let γ : ℝ → M := fun t => e (t • v)
  have hγsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a 1) := by
    have hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞
        (fun t : ℝ => t • v) :=
      contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
    apply (he.comp hsmooth.contMDiffOn ?_).of_le (by simp)
    intro t ht
    exact radial_mem_ball_of_mem_ball hv ⟨ha.1.trans ht.1, ht.2⟩
  have hlen : g.pathELength γ a 1 =
      ENNReal.ofReal ‖v‖ * ENNReal.ofReal (1 - a) := by
    apply g.pathELength_eq_of_tangentNorm_eq
    intro t ht
    exact hspeed t ⟨ha.1.trans ht.1, ht.2⟩
  have hdist := g.edist_le_pathELength_of_mem_Icc hγsmooth
    (show (1 : ℝ) ∈ Icc a 1 by exact ⟨ha.2, le_rfl⟩)
  rw [hlen] at hdist
  simpa only [γ, one_smul] using hdist

omit [MeasurableSpace M] [BorelSpace M] in

theorem radial_minimizing_star
    (g : PoincareConjecture.RiemannianMetric n M)
    {p : M}
    {R : ℝ} {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ localMinimizingSet (fun w => g.edist p (e w)) R)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖)
    (hdist : ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) :
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      a • v ∈ localMinimizingSet (fun w => g.edist p (e w)) R := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  intro a ha0 ha1
  have hva : a • v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    exact radial_mem_ball_of_mem_ball hv.1 ⟨ha0, ha1⟩
  refine ⟨hva, ?_⟩
  have hupper := hdist a ⟨ha0, ha1⟩
  have hseg := radial_subsegment_upper g he hv.1 hspeed ⟨ha0, ha1⟩
  have htri := Manifold.riemannianEDist_triangle (I := 𝓡 n)
    (x := p) (y := e (a • v)) (z := e v)
  change g.edist p (e v) ≤
      g.edist p (e (a • v)) + g.edist (e (a • v)) (e v) at htri
  have hsum : ENNReal.ofReal ‖v‖ ≤
      g.edist p (e (a • v)) +
        ENNReal.ofReal ‖v‖ * ENNReal.ofReal (1 - a) := by
    change v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ∧
      g.edist p (e v) = ENNReal.ofReal ‖v‖ at hv
    rw [hv.2] at htri
    exact htri.trans (add_le_add le_rfl hseg)
  have hsum' : ENNReal.ofReal (a * ‖v‖) +
      ENNReal.ofReal ((1 - a) * ‖v‖) ≤
      g.edist p (e (a • v)) + ENNReal.ofReal ((1 - a) * ‖v‖) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) (norm_nonneg v))
      (mul_nonneg (sub_nonneg.mpr ha1) (norm_nonneg v))]
    convert hsum using 1
    · congr 1
      ring
    · apply congrArg (fun z : ℝ≥0∞ =>
        g.edist p (e (a • v)) + z)
      simpa only [mul_comm] using
        (ENNReal.ofReal_mul' (p := 1 - a) (q := ‖v‖)
          (norm_nonneg v))
  have hlow : ENNReal.ofReal (a * ‖v‖) ≤ g.edist p (e (a • v)) :=
    ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hsum'
  have hupp : g.edist p (e (a • v)) ≤ ENNReal.ofReal (a * ‖v‖) := by
    calc
      g.edist p (e (a • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal a := hupper
      _ = ENNReal.ofReal (a * ‖v‖) := by
        simpa only [mul_comm] using
          (ENNReal.ofReal_mul' (p := a) (q := ‖v‖) (norm_nonneg v)).symm
  change g.edist p (e (a • v)) = ENNReal.ofReal ‖a • v‖
  simpa only [norm_smul, Real.norm_of_nonneg ha0] using (le_antisymm hupp hlow)

theorem exists_precompact_polar_cut_null
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) {R : ℝ}
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
          (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0 := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p hR hcompact
  let d : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun v => g.edist p (e v)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hd : ContinuousOn d (Metric.ball 0 R) := by
    change ContinuousOn (fun v => EDist.edist p (e v)) (Metric.ball 0 R)
    exact continuous_edist.continuousOn.comp
      (continuous_const.continuousOn.prodMk he.continuousOn)
      (fun _ _ => Set.mem_univ _)
  let S : Set (EuclideanSpace ℝ (Fin n)) := localMinimizingSet d R
  have hS : MeasurableSet S := measurableSet_localMinimizingSet hd
  have hSball : S ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro v hv
    exact hv.1
  have hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S := by
    intro v hv a ha0 ha1
    exact radial_minimizing_star g he hv
      (fun t ht => ((hgeo v hv.1).2 t ht).1)
      (fun t ht => ((hgeo v hv.1).2 t ht).2)
      a ha0 ha1
  refine ⟨L, e, hL, he, he0, hed, hgeo, ?_⟩
  exact volumeMeasure_image_eq_zero_terminalRadialPoints g e he hS hSball hstar

end Poincare.VolumeComparison
