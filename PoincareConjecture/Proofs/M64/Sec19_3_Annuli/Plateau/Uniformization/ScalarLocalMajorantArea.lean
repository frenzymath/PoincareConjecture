import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalMetricMajorant
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarRegularizedArea
import PoincareConjecture.Proofs.M60.Mathlib.UniformizationPositiveForms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Form" => Plane →L[ℝ] Plane →L[ℝ] ℝ

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalarC1_AreaGram_continuousOn
    (g : RiemannianMetric n M) {f : Plane → M} {U : Set Plane}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) :
    ContinuousOn (m60AreaGram g f) U := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hA := scalarC1_pullback_continuousOn g f hU hf
  exact (hA.clm_apply continuousOn_const).clm_apply continuousOn_const

theorem scalarC1_EnergyDensity_continuousOn
    (g : RiemannianMetric n M) {f : Plane → M} {U : Set Plane}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) :
    ContinuousOn (m60EnergyDensity g f) U := by
  have hG := scalarC1_AreaGram_continuousOn g hU hf
  have hentry (i j : Fin 2) : ContinuousOn (fun p => m60AreaGram g f p i j) U :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hG)
  unfold m60EnergyDensity
  simp only [Matrix.trace_fin_two]
  exact continuousOn_const.mul ((hentry 0 0).add (hentry 1 1))

theorem scalarLocalC1_majorant_area_tendsto
    (g : RiemannianMetric n M) (f : Plane → M)
    {K U : Set Plane} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    (q : ℕ → RiemannianMetric 2 Plane)
    (hbound : ∀ k p, p ∈ K → ∀ v : Plane,
      M60.metricPullbackForm (n := 2) g f p v v ≤ (q k).inner p v v ∧
      (q k).inner p v v ≤ M60.metricPullbackForm (n := 2) g f p v v +
        (2 * ((k : ℝ) + 1)⁻¹) * ‖v‖ ^ 2) :
    Tendsto (fun k => ∫ p in K, m60AreaDensity (q k) id p) atTop
      (𝓝 (∫ p in K, m60AreaDensity g f p)) := by
  have hd : Tendsto (fun k : ℕ => 2 * ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have hd₀ : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using hd₀.const_mul 2
  have hcoef (p : Plane) (hp : p ∈ K) (i j : Fin 2) :
      Tendsto (fun k => m60AreaGram (q k) id p i j) atTop
        (𝓝 (m60AreaGram g f p i j)) := by
    have h := M60.tendsto_bilinear_of_quadratic_bounds (E := Plane)
      (show Form from M60.metricPullbackForm (n := 2) g f p) (innerSL ℝ)
      (fun k => (show Form from (q k).inner p))
      (fun v w => g.symm _ _ _) (fun k => (q k).symm _) hd
      (fun k v => by
        change M60.metricPullbackForm (n := 2) g f p v v ≤ (q k).inner p v v ∧
          (q k).inner p v v ≤ M60.metricPullbackForm (n := 2) g f p v v +
            (2 * ((k : ℝ) + 1)⁻¹) * inner ℝ v v
        rw [real_inner_self_eq_norm_sq]
        exact hbound k p hp v)
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)
    simpa only [m60AreaGram, mfderiv_id, ContinuousLinearMap.id_apply, id_eq,
      M60.metricPullbackForm_apply] using! h
  have hpoint (p : Plane) (hp : p ∈ K) :
      Tendsto (fun k => m60AreaDensity (q k) id p) atTop
        (𝓝 (m60AreaDensity g f p)) := by
    have hdet := ((hcoef p hp 0 0).mul (hcoef p hp 1 1)).sub
      ((hcoef p hp 0 1).mul (hcoef p hp 1 0))
    simpa only [m60AreaDensity, Matrix.det_fin_two] using
      ((show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds).max hdet).sqrt
  have hdom (k : ℕ) (p : Plane) (hp : p ∈ K) :
      m60AreaDensity (q k) id p ≤ m60EnergyDensity g f p + 2 := by
    have hdiag (i : Fin 2) : m60AreaGram (q k) id p i i ≤
        m60AreaGram g f p i i + 2 * ((k : ℝ) + 1)⁻¹ := by
      have h := (hbound k p hp (EuclideanSpace.basisFun (Fin 2) ℝ i)).2
      simpa only [m60AreaGram, mfderiv_id, ContinuousLinearMap.id_apply, id_eq,
        M60.metricPullbackForm_apply, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one,
        one_pow, mul_one] using! h
    have henergy : m60EnergyDensity (q k) id p ≤
        m60EnergyDensity g f p + 2 * ((k : ℝ) + 1)⁻¹ := by
      simp only [m60EnergyDensity, Matrix.trace_fin_two]
      linarith [hdiag 0, hdiag 1]
    have hk : ((k : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by have h := Nat.cast_nonneg (α := ℝ) k; linarith)
    exact (m60AreaDensity_le_energyDensity (q k) id p).trans (henergy.trans (by linarith))
  apply tendsto_integral_of_dominated_convergence (fun p => m60EnergyDensity g f p + 2)
  · intro k
    exact (m60AreaDensity_continuous (q k) contMDiff_id).aestronglyMeasurable
  · have hmajor : ContinuousOn (fun p => m60EnergyDensity g f p + 2) K :=
      ((scalarC1_EnergyDensity_continuousOn g hU hf).add continuousOn_const).mono hKU
    exact hmajor.integrableOn_compact hK
  · intro k
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    rw [Real.norm_of_nonneg (m60AreaDensity_nonneg (q k) id p)]
    exact hdom k p hp
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact hpoint p hp

theorem scalarLocalC1_exists_metric_majorant_area_lt
    (g : RiemannianMetric n M) (f : Plane → M)
    {K U : Set Plane} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) (eta : ℝ) (heta : 0 < eta) :
    ∃ q : RiemannianMetric 2 Plane,
      (∀ p ∈ K, ∀ v : Plane,
        g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
          q.inner p v v) ∧
      (∫ p in K, m60AreaDensity q id p) < (∫ p in K, m60AreaDensity g f p) + eta := by
  choose q hq using fun k : ℕ => scalarLocalC1_exists_smooth_metric_majorant g f hK hU hKU hf
    ((k : ℝ) + 1)⁻¹ (by positivity)
  have hbound (k : ℕ) (p : Plane) (hp : p ∈ K) (v : Plane) :
      M60.metricPullbackForm (n := 2) g f p v v ≤ (q k).inner p v v ∧
      (q k).inner p v v ≤ M60.metricPullbackForm (n := 2) g f p v v +
        (2 * ((k : ℝ) + 1)⁻¹) * ‖v‖ ^ 2 := by
    exact ⟨(le_add_of_nonneg_right (by positivity)).trans (hq k p hp v).1, (hq k p hp v).2⟩
  have hevent := (scalarLocalC1_majorant_area_tendsto g f hK hU hKU hf q hbound).eventually
    (gt_mem_nhds (show (∫ p in K, m60AreaDensity g f p) <
      (∫ p in K, m60AreaDensity g f p) + eta by linarith))
  obtain ⟨k, hk⟩ := hevent.exists
  exact ⟨q k, fun p hp v => (hbound k p hp v).1, hk⟩

end PoincareConjecture.M64Uniformization
