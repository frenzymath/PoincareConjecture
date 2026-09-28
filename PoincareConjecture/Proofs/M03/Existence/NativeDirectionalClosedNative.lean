import PoincareConjecture.Proofs.M03.Existence.ChartDirectionalNative
import PoincareConjecture.Proofs.M03.Existence.ChartLpNative
import PoincareConjecture.Proofs.M03.Existence.ChartMeasureDetectionNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanSmoothCoefficientClosedNative

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

noncomputable section

universe u v

namespace PoincareConjecture.TensorProbeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

def scalarDirectional (V : SmoothField (n := n) (M := M)) (f : M → ℝ) (x : M) : ℝ :=
  mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (V x)

theorem chart_directional_limit_zero
    (p : M) (V : SmoothField (n := n) (M := M)) {μ : Measure M}
    {A : Set ModelE} (hA : IsOpen A) (hAt : A ⊆ (chartAt ModelE p).target)
    {c : ℝ} (hc : 0 < c)
    (hdom : ENNReal.ofReal c • (volume.restrict A).map (chartAt ModelE p).symm ≤ μ)
    (f : ℕ → M → ℝ) (hf : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j))
    (hfLp : ∀ j, MemLp (f j) 2 μ)
    (hDfLp : ∀ j, MemLp (scalarDirectional V (f j)) 2 μ)
    (w : Lp ℝ 2 μ)
    (hflim : Tendsto (fun j => (hfLp j).toLp (f j)) atTop (𝓝 0))
    (hDflim : Tendsto (fun j => (hDfLp j).toLp (scalarDirectional V (f j)))
      atTop (𝓝 w)) :
    ChartLpNative.chartPullbackL2 (chartAt ModelE p) hA.measurableSet hAt hc hdom w = 0 := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict A) :=
    ChartLpNative.chartPullbackL2 e hA.measurableSet hAt hc hdom
  let g : ℕ → ModelE → ℝ := fun j => f j ∘ e.symm
  let a : Fin n → ModelE → ℝ := fun i z => chartField p V z i
  let v : Fin n → ModelE := (PiLp.basisFun 2 ℝ (Fin n))
  let Ag : ℕ → ModelE → ℝ := fun j z => ∑ i, a i z * fderiv ℝ (g j) z (v i)
  have hg (j : ℕ) : ContDiffOn ℝ ∞ (g j) A :=
    (contDiffOn_scalar_chartInverse p (hf j)).mono hAt
  have ha (i : Fin n) : ContDiffOn ℝ ∞ (a i) A :=
    (contDiffOn_chartField_coordinate p V i).mono hAt
  have hvalue (j : ℕ) : L ((hfLp j).toLp (f j)) =ᵐ[volume.restrict A] g j :=
    ChartLpNative.chartPullbackL2_toLp_coe e hA.measurableSet hAt hc hdom (hfLp j)
  have hderivative (j : ℕ) : L ((hDfLp j).toLp (scalarDirectional V (f j)))
      =ᵐ[volume.restrict A] Ag j := by
    apply (ChartLpNative.chartPullbackL2_toLp_coe e hA.measurableSet hAt hc hdom
      (hDfLp j)).trans
    filter_upwards [ae_restrict_mem hA.measurableSet] with z hz
    exact directional_eq_chart_firstOrder p V (hf j) (hAt hz)
  have hgLp (j : ℕ) : MemLp (g j) 2 (volume.restrict A) :=
    MemLp.ae_eq (hvalue j) (Lp.memLp (L ((hfLp j).toLp (f j))))
  have hAgLp (j : ℕ) : MemLp (Ag j) 2 (volume.restrict A) :=
    MemLp.ae_eq (hderivative j)
      (Lp.memLp (L ((hDfLp j).toLp (scalarDirectional V (f j)))))
  have hvalueEq (j : ℕ) : L ((hfLp j).toLp (f j)) = (hgLp j).toLp (g j) := by
    apply Lp.ext
    exact (hvalue j).trans (hgLp j).coeFn_toLp.symm
  have hderivativeEq (j : ℕ) : L ((hDfLp j).toLp (scalarDirectional V (f j))) =
      (hAgLp j).toLp (Ag j) := by
    apply Lp.ext
    exact (hderivative j).trans (hAgLp j).coeFn_toLp.symm
  have hglim : Tendsto (fun j => (hgLp j).toLp (g j)) atTop (𝓝 0) := by
    have h := ((L.continuous.tendsto 0).comp hflim).congr'
      (Eventually.of_forall hvalueEq)
    simpa only [map_zero] using h
  have hAglim : Tendsto (fun j => (hAgLp j).toLp (Ag j)) atTop (𝓝 (L w)) :=
    ((L.continuous.tendsto w).comp hDflim).congr' (Eventually.of_forall hderivativeEq)
  exact EuclideanDerivativeNative.local_smoothFirstOrder_limit_zero hA a ha v
    g hg hgLp hAgLp (L w) hglim hAglim

variable {iota : Type v} [Finite iota]

theorem scalarDirectional_limit_zero
    (p : iota → M) (φ : iota → C(M, ℝ))
    (V : SmoothField (n := n) (M := M))
    (f : ℕ → M → ℝ) (hf : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j))
    (hfLp : ∀ j, MemLp (f j) 2
      (Measure.sum (fun i => ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i))))
    (hDfLp : ∀ j, MemLp (scalarDirectional V (f j)) 2
      (Measure.sum (fun i => ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i))))
    (w : Lp ℝ 2
      (Measure.sum (fun i => ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i))))
    (hflim : Tendsto (fun j => (hfLp j).toLp (f j)) atTop (𝓝 0))
    (hDflim : Tendsto (fun j => (hDfLp j).toLp (scalarDirectional V (f j)))
      atTop (𝓝 w)) : w = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply ChartMeasureNative.ae_zero_sumWeightedChart_of_positiveRegion
    (fun i => chartAt ModelE (p i)) φ (Lp.stronglyMeasurable w).measurable
  intro i k
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE (p i)
  let A : Set ModelE := ChartMeasureNative.positiveRegion e (φ i) k
  have hA : IsOpen A := ChartMeasureNative.positiveRegion_open e (φ i) k
  have hAt : A ⊆ e.target := ChartMeasureNative.positiveRegion_subset_target e (φ i) k
  have hc : 0 < 1 / (k + 1 : ℝ) := div_pos zero_lt_one (Nat.cast_add_one_pos k)
  have hdom : ENNReal.ofReal (1 / (k + 1 : ℝ)) • (volume.restrict A).map e.symm ≤
      Measure.sum (fun i => ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i)) :=
    (ChartMeasureNative.positiveRegion_lower e (φ i) k).trans
      (Measure.le_sum (fun i =>
        ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i)) i)
  have hzero := chart_directional_limit_zero (p i) V hA hAt hc hdom
    f hf hfLp hDfLp w hflim hDflim
  have hcoe := ChartLpNative.chartPullbackL2_coe e hA.measurableSet hAt hc hdom w
  rw [hzero] at hcoe
  exact hcoe.symm.trans (Lp.coeFn_zero ℝ 2 (volume.restrict A))

end PoincareConjecture.TensorProbeNative
