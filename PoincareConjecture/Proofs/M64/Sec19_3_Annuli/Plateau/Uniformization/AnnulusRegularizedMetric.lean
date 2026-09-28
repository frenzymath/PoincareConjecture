import PoincareConjecture.Proofs.M60.Mathlib.MetricPullbackForm
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.MeasureTheory.Integral.DominatedConvergence













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

noncomputable section

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private def regularizationPlaneMetric : RiemannianMetric 2 LoopPlane :=
  { riemannianMetricVectorSpace LoopPlane with
    contMDiff := (riemannianMetricVectorSpace LoopPlane).contMDiff.of_le le_top }

private theorem planar_pullback_nonneg (g : RiemannianMetric n M)
    (f : LoopPlane → M) (p v : LoopPlane) :
    0 ≤ M60.metricPullbackForm (n := 2) g f p v v := by
  change 0 ≤ g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
    (mfderiv (𝓡 2) (𝓡 n) f p v)
  by_cases hv : mfderiv (𝓡 2) (𝓡 n) f p v = 0
  · simp [hv]
  · exact (g.pos _ _ hv).le







def m64RegularizedPullbackMetric (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) : RiemannianMetric 2 LoopPlane where
  inner p := M60.metricPullbackForm (n := 2) g f p +
    delta • regularizationPlaneMetric.inner p
  symm p v w := by
    change g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
        (mfderiv (𝓡 2) (𝓡 n) f p w) + delta * inner ℝ v w = _
    rw [g.symm, real_inner_comm]
    rfl
  pos p v hv := add_pos_of_nonneg_of_pos (planar_pullback_nonneg g f p v)
    (mul_pos hdelta (regularizationPlaneMetric.pos p v hv))
  isVonNBounded p := by
    let L : LoopPlane →L[ℝ] LoopPlane :=
      (Real.sqrt delta)⁻¹ • ContinuousLinearMap.id ℝ LoopPlane
    refine ((regularizationPlaneMetric.isVonNBounded p).image L).subset ?_
    intro v hv
    refine ⟨Real.sqrt delta • v, ?_, ?_⟩
    · change regularizationPlaneMetric.inner p (Real.sqrt delta • v)
        (Real.sqrt delta • v) < 1
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, Real.mul_self_sqrt hdelta.le]
      have h := planar_pullback_nonneg g f p v
      change M60.metricPullbackForm (n := 2) g f p v v +
        delta * regularizationPlaneMetric.inner p v v < 1 at hv
      linarith
    · change (Real.sqrt delta)⁻¹ • (Real.sqrt delta • v) = v
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hdelta), one_smul]
  contMDiff p := (M60.metricPullbackForm_contMDiffAt g (hf p)).add_section
    ((regularizationPlaneMetric.contMDiff p).const_smul_section (a := delta))






theorem m64RegularizedPullbackMetric_inner (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p v w : LoopPlane) :
    (m64RegularizedPullbackMetric g f hf delta hdelta).inner p v w =
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
        (mfderiv (𝓡 2) (𝓡 n) f p w) + delta * inner ℝ v w := rfl







theorem m64RegularizedPullbackMetric_dominates (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p v : LoopPlane) :
    g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
        (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
      (m64RegularizedPullbackMetric g f hf delta hdelta).inner p v v := by
  rw [m64RegularizedPullbackMetric_inner]
  exact le_add_of_nonneg_right (mul_nonneg hdelta.le (real_inner_self_nonneg (x := v)))







theorem m64RegularizedPullbackMetric_gram (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p : LoopPlane) (i j : Fin 2) :
    m60AreaGram (m64RegularizedPullbackMetric g f hf delta hdelta) id p i j =
      m60AreaGram g f p i j + delta *
        inner ℝ (EuclideanSpace.basisFun (Fin 2) ℝ i)
          (EuclideanSpace.basisFun (Fin 2) ℝ j) := by
  simp only [m60AreaGram, mfderiv_id, ContinuousLinearMap.id_apply,
    m64RegularizedPullbackMetric_inner, id_eq]







theorem m64RegularizedPullbackMetric_energyDensity (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p : LoopPlane) :
    m60EnergyDensity (m64RegularizedPullbackMetric g f hf delta hdelta) id p =
      m60EnergyDensity g f p + delta := by
  simp only [m60EnergyDensity, Matrix.trace_fin_two, m64RegularizedPullbackMetric_gram,
    real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one,
    one_pow, mul_one]
  ring







theorem m64RegularizedPullbackMetric_det (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (p : LoopPlane) :
    Matrix.det (m60AreaGram (m64RegularizedPullbackMetric g f hf delta hdelta) id p) =
      Matrix.det (m60AreaGram g f p) + 2 * delta * m60EnergyDensity g f p +
        delta ^ 2 := by
  simp only [Matrix.det_fin_two, m64RegularizedPullbackMetric_gram,
    m60EnergyDensity, Matrix.trace_fin_two]
  norm_num [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]
  ring






theorem m64RegularizedPullbackMetric_areaDensity_bound (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1) (p : LoopPlane) :
    m60AreaDensity (m64RegularizedPullbackMetric g f hf delta hdelta) id p ≤
      m60EnergyDensity g f p + 1 := by
  calc
    _ ≤ m60EnergyDensity (m64RegularizedPullbackMetric g f hf delta hdelta) id p :=
      m60AreaDensity_le_energyDensity _ _ _
    _ = m60EnergyDensity g f p + delta :=
      m64RegularizedPullbackMetric_energyDensity g f hf delta hdelta p
    _ ≤ _ := add_le_add_right hdelta' _







theorem m64RegularizedPullbackMetric_area_tendsto (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    {K : Set LoopPlane} (hK : IsCompact K) :
    Tendsto (fun k : ℕ => ∫ p in K, m60AreaDensity
      (m64RegularizedPullbackMetric g f hf ((k : ℝ) + 1)⁻¹ (by positivity)) id p)
      atTop (𝓝 (∫ p in K, m60AreaDensity g f p)) := by
  let q (k : ℕ) := m64RegularizedPullbackMetric g f hf ((k : ℝ) + 1)⁻¹ (by positivity)
  have hd : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hpoint (p : LoopPlane) :
      Tendsto (fun k : ℕ => m60AreaDensity (q k) id p)
        atTop (𝓝 (m60AreaDensity g f p)) := by
    simp only [m60AreaDensity, q, m64RegularizedPullbackMetric_det]
    have hc : Tendsto (fun _ : ℕ => Matrix.det (m60AreaGram g f p))
        atTop (𝓝 (Matrix.det (m60AreaGram g f p))) := tendsto_const_nhds
    have hdet := (hc.add ((hd.const_mul 2).mul_const (m60EnergyDensity g f p))).add
      (hd.pow 2)
    simpa only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] using
      ((show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds).max hdet).sqrt
  apply tendsto_integral_of_dominated_convergence (fun p => m60EnergyDensity g f p + 1)
  · intro k
    exact (m60AreaDensity_continuous (q k) contMDiff_id).aestronglyMeasurable
  · exact ((m60EnergyDensity_continuous g (hf.of_le (by simp))).add
      continuous_const).continuousOn.integrableOn_compact hK
  · intro k
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (m60AreaDensity_nonneg (q k) id p)]
    apply m64RegularizedPullbackMetric_areaDensity_bound
    exact inv_le_one_of_one_le₀ (by have h := Nat.cast_nonneg (α := ℝ) k; linarith)
  · exact Filter.Eventually.of_forall hpoint







theorem m64RegularizedPullbackMetric_exists_area_lt (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    {K : Set LoopPlane} (hK : IsCompact K) (eta : ℝ) (heta : 0 < eta) :
    ∃ (delta : ℝ) (hdelta : 0 < delta),
      (∫ p in K, m60AreaDensity (m64RegularizedPullbackMetric g f hf delta hdelta) id p) <
        (∫ p in K, m60AreaDensity g f p) + eta := by
  have hevent := (m64RegularizedPullbackMetric_area_tendsto g f hf hK).eventually
    (gt_mem_nhds (show (∫ p in K, m60AreaDensity g f p) <
      (∫ p in K, m60AreaDensity g f p) + eta by linarith))
  obtain ⟨k, hk⟩ := hevent.exists
  exact ⟨((k : ℝ) + 1)⁻¹, by positivity, hk⟩

end PoincareConjecture
