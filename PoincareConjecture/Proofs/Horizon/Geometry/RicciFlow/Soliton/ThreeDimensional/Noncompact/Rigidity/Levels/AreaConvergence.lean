import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.CompactImage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem area_le_of_quadraticForm_le (g h : RiemannianMetric 2 M)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      h.inner x v v ≤ c * g.inner x v v) :
    h.volumeMeasure.real univ ≤ c * g.volumeMeasure.real univ := by
  have hnorm (x : M) (v : TangentSpace (𝓡 2) x) :
      h.tangentNorm x v ≤ Real.sqrt c * g.tangentNorm x v := by
    change Real.sqrt (h.inner x v v) ≤ Real.sqrt c * Real.sqrt (g.inner x v v)
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt (hbound x v)
  have hvol := g.volumeMeasure_image_le_of_tangentNorm_le_on_compact h
    (f := id) (U := univ) (s := univ) isOpen_univ isCompact_univ (Subset.refl _)
    contMDiff_id.contMDiffOn (Real.sqrt_pos.mpr hc) (by
      intro x _ v
      simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using hnorm x v)
  simp only [image_id, ← ENNReal.ofReal_pow (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at hvol
  have hfinite : ENNReal.ofReal c * g.volumeMeasure univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g.volumeMeasure_lt_top_of_isCompact isCompact_univ).ne
  have hreal := ENNReal.toReal_mono hfinite hvol
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using hreal



theorem area_bounds_of_relative_quadraticForm_error (g h : RiemannianMetric 2 M)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (herror : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      |h.inner x v v - g.inner x v v| ≤ ε * g.inner x v v) :
    (1 - ε) * g.volumeMeasure.real univ ≤ h.volumeMeasure.real univ ∧
      h.volumeMeasure.real univ ≤ (1 + ε) * g.volumeMeasure.real univ := by
  have hupper : h.volumeMeasure.real univ ≤ (1 + ε) * g.volumeMeasure.real univ := by
    apply g.area_le_of_quadraticForm_le h (by linarith)
    intro x v
    have he := (le_abs_self (h.inner x v v - g.inner x v v)).trans (herror x v)
    linarith
  have hlower : g.volumeMeasure.real univ ≤ (1 - ε)⁻¹ * h.volumeMeasure.real univ := by
    apply h.area_le_of_quadraticForm_le g (inv_pos.mpr (sub_pos.mpr hε1))
    intro x v
    have he := (neg_le_abs (h.inner x v v - g.inner x v v)).trans (herror x v)
    rw [mul_comm ((1 - ε)⁻¹)]
    apply (le_mul_inv_iff₀ (sub_pos.mpr hε1)).mpr
    linarith
  refine ⟨?_, hupper⟩
  have hh := mul_le_mul_of_nonneg_left hlower (sub_pos.mpr hε1).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hε1).ne', one_mul] using hh



theorem tendsto_area_of_uniform_relative_quadraticForm_error
    {ι : Type*} {l : Filter ι} (gseq : ι → RiemannianMetric 2 M) (g : RiemannianMetric 2 M)
    (hmetric : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        |(gseq i).inner x v v - g.inner x v v| ≤ ε * g.inner x v v) :
    Tendsto (fun i => (gseq i).volumeMeasure.real univ) l (𝓝 (g.volumeMeasure.real univ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := g.volumeMeasure.real univ
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  let δ := min (1 / 2) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hh : δ * (A + 1) ≤ ε :=
      (le_div_iff₀ (by linarith : 0 < A + 1)).mp (min_le_right _ _)
    nlinarith
  filter_upwards [hmetric δ hδ] with i hi
  obtain ⟨hlower, hupper⟩ := g.area_bounds_of_relative_quadraticForm_error (gseq i) hδ hδ1 hi
  have harea : |(gseq i).volumeMeasure.real univ - A| ≤ δ * A := by
    apply abs_le.mpr
    constructor <;> dsimp only [A] at * <;> nlinarith
  rw [Real.dist_eq]
  exact harea.trans_lt hδA



theorem tendsto_volumeMeasure_univ_of_uniform_relative_quadraticForm_error
    {ι : Type*} {l : Filter ι} (gseq : ι → RiemannianMetric 2 M) (g : RiemannianMetric 2 M)
    (hmetric : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        |(gseq i).inner x v v - g.inner x v v| ≤ ε * g.inner x v v) :
    Tendsto (fun i => (gseq i).volumeMeasure univ) l (𝓝 (g.volumeMeasure univ)) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_area_of_uniform_relative_quadraticForm_error gseq g hmetric)
  simpa only [Function.comp_def, Measure.real, ENNReal.ofReal_toReal
    (g.volumeMeasure_lt_top_of_isCompact isCompact_univ).ne,
    ENNReal.ofReal_toReal ((gseq _).volumeMeasure_lt_top_of_isCompact isCompact_univ).ne] using h

end PoincareConjecture.RiemannianMetric
