import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.RadialNull
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.NullImage

set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Manifold ContDiff Bundle

namespace Poincare.VolumeComparison

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def terminalRadialPoints (S : Set E) (R : ℝ) : Set E :=
  S ∩ ({v | v ≠ 0} ∩ ⋂ q : ℚ,
    {v | ¬ (1 < (q : ℝ) ∧ (q : ℝ) * ‖v‖ < R ∧ (q : ℝ) • v ∈ S)})

theorem measurableSet_terminalRadialPoints {S : Set E} {R : ℝ}
    (hS : MeasurableSet S) :
    MeasurableSet (terminalRadialPoints S R) := by
  rw [terminalRadialPoints]
  refine hS.inter ((measurableSet_singleton (0 : E)).compl.inter ?_)
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.compl
  have hq : MeasurableSet {v : E | (1 : ℝ) < (q : ℝ)} :=
    measurableSet_lt measurable_const measurable_const
  have hnorm : MeasurableSet {v : E | (q : ℝ) * ‖v‖ < R} :=
    measurableSet_lt (measurable_const.mul measurable_norm) measurable_const
  have hsmul : MeasurableSet {v : E | (q : ℝ) • v ∈ S} :=
    hS.preimage (measurable_const_smul (q : ℝ))
  exact hq.inter (hnorm.inter hsmul)

theorem terminalRadialPoints_subset {S : Set E} {R : ℝ} :
    terminalRadialPoints S R ⊆ S := by
  intro v hv
  exact hv.1

theorem zero_not_mem_terminalRadialPoints {S : Set E} {R : ℝ} :
    (0 : E) ∉ terminalRadialPoints S R := by
  intro h
  exact h.2.1 rfl

theorem isRadialGraph_terminalRadialPoints {S : Set E} {R : ℝ}
    (hS : S ⊆ Metric.ball (0 : E) R)
    (hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S) :
    IsRadialGraph (terminalRadialPoints S R) := by
  intro u hu r₁ r₂ hr₁ hr₂ h₁ h₂
  have hcontra : ∀ {a b : ℝ}, 0 < a → 0 < b → a < b →
      a • u ∈ terminalRadialPoints S R → b • u ∈ terminalRadialPoints S R → False := by
    intro a b ha hb hab haT hbT
    obtain ⟨q, hq1, hqr⟩ := exists_rat_btwn (show (1 : ℝ) < b / a by
      exact (lt_div_iff₀ ha).2 (by simpa using hab))
    have hqpos : 0 ≤ (q : ℝ) := by linarith
    have hqmul : (q : ℝ) * a < b := by
      exact (lt_div_iff₀ ha).1 (by simpa using hqr)
    have hbR : b < R := by
      have := mem_ball_zero_iff.mp (hS hbT.1)
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hb, mem_sphere_zero_iff_norm.mp hu]
        using this
    have hqR : (q : ℝ) * ‖a • u‖ < R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha,
        mem_sphere_zero_iff_norm.mp hu]
      simpa using hqmul.trans hbR
    have hscale : (q : ℝ) • (a • u) =
        ((q : ℝ) * a / b) • (b • u) := by
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
    have hcoef0 : 0 ≤ (q : ℝ) * a / b :=
      div_nonneg (mul_nonneg hqpos ha.le) hb.le
    have hcoef1 : (q : ℝ) * a / b ≤ 1 := by
      exact (div_le_one hb).2 (by linarith)
    have hqmem : (q : ℝ) • (a • u) ∈ S := by
      rw [hscale]
      exact hstar (b • u) hbT.1 _ hcoef0 hcoef1
    exact (Set.mem_iInter.mp haT.2.2 q) ⟨hq1, hqR, hqmem⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hcontra hr₁ hr₂ hlt h₁ h₂
  · exact hcontra hr₂ hr₁ hgt h₂ h₁

theorem addHaar_eq_zero_terminalRadialPoints
    {S : Set E} {R : ℝ} (μ : Measure E) [μ.IsAddHaarMeasure]
    (hS : MeasurableSet S)
    (hSball : S ⊆ Metric.ball (0 : E) R)
    (hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S) :
    μ (terminalRadialPoints S R) = 0 := by
  apply addHaar_eq_zero_of_isRadialGraph μ
    (measurableSet_terminalRadialPoints hS)
    zero_not_mem_terminalRadialPoints
    (isRadialGraph_terminalRadialPoints hSball hstar)

def localMinimizingSet (d : E → ℝ≥0∞) (R : ℝ) : Set E :=
  Metric.ball (0 : E) R ∩ {v | d v = ENNReal.ofReal ‖v‖}

theorem measurableSet_localMinimizingSet
    {d : E → ℝ≥0∞} {R : ℝ}
    (hd : ContinuousOn d (Metric.ball (0 : E) R)) :
    MeasurableSet (localMinimizingSet d R) := by
  classical
  let U : Set E := Metric.ball (0 : E) R
  let d' : E → ℝ≥0∞ := U.piecewise d 0
  have hd' : Measurable d' := by
    apply ContinuousOn.measurable_piecewise hd
    exact continuousOn_const
    exact Metric.isOpen_ball.measurableSet
  have hn : Measurable (fun v : E => ENNReal.ofReal ‖v‖) :=
    ENNReal.continuous_ofReal.measurable.comp measurable_norm
  have heq : MeasurableSet {v : E | d' v = ENNReal.ofReal ‖v‖} :=
    measurableSet_eq_fun hd' hn
  have hrewrite : localMinimizingSet d R = U ∩ {v | d' v = ENNReal.ofReal ‖v‖} := by
    ext v
    by_cases hv : v ∈ U <;> simp [localMinimizingSet, U, d', hv]
  rw [hrewrite]
  exact Metric.isOpen_ball.measurableSet.inter heq

theorem volumeMeasure_image_eq_zero_terminalRadialPoints
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M)
    {R : ℝ}
    (e : EuclideanSpace ℝ (Fin n) → M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S)
    (hSball : S ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    (hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S) :
    g.volumeMeasure (e '' terminalRadialPoints S R) = 0 := by
  apply g.volumeMeasure_image_eq_zero_of_mdifferentiableAt
    (fun x hx =>
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds
        (hSball (terminalRadialPoints_subset hx)))).mdifferentiableAt (by simp))
  exact addHaar_eq_zero_terminalRadialPoints (volume : Measure (EuclideanSpace ℝ (Fin n)))
    hS hSball hstar

end Poincare.VolumeComparison
