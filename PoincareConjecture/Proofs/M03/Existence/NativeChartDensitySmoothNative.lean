import PoincareConjecture.Proofs.M03.Existence.ChartTransitionJacobianNative
import PoincareConjecture.Proofs.M03.Existence.ChartDirectionalNative









set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def chartWeightDensity (p q : M) (φ : M → ℝ) : E → ℝ :=
  (chartTransition p q).source.indicator
    (fun z => φ ((chartAt E p).symm z) * chartTransitionJacobian p q z)

theorem chartWeightDensity_of_mem (p q : M) (φ : M → ℝ) {z : E}
    (hz : z ∈ chartTransitionDomain p q) :
    chartWeightDensity p q φ z = φ ((chartAt E p).symm z) * chartTransitionJacobian p q z :=
  indicator_of_mem hz _

theorem chartWeightDensity_of_notMem (p q : M) (φ : M → ℝ) {z : E}
    (hz : z ∉ chartTransitionDomain p q) : chartWeightDensity p q φ z = 0 :=
  indicator_of_notMem hz _

theorem chartWeightDensity_nonneg (p q : M) {φ : M → ℝ} (hφ : ∀ x, 0 ≤ φ x) (z : E) :
    0 ≤ chartWeightDensity p q φ z := by
  by_cases hz : z ∈ chartTransitionDomain p q
  · rw [chartWeightDensity_of_mem p q φ hz]
    exact mul_nonneg (hφ _) (chartTransitionJacobian_nonneg p q z)
  · rw [chartWeightDensity_of_notMem p q φ hz]


theorem chartWeightDensity_pos_of_weight_pos (p q : M) {φ : M → ℝ}
    (hsupport : tsupport φ ⊆ (chartAt E q).source) {z : E}
    (hz : z ∈ (chartAt E p).target) (hφ : 0 < φ ((chartAt E p).symm z)) :
    0 < chartWeightDensity p q φ z := by
  have hxq : (chartAt E p).symm z ∈ (chartAt E q).source :=
    hsupport (subset_tsupport φ hφ.ne')
  have hzU : z ∈ chartTransitionDomain p q := ⟨hz, hxq⟩
  rw [chartWeightDensity_of_mem p q φ hzU]
  exact mul_pos hφ (chartTransitionJacobian_pos p q hzU)


theorem chartWeightDensity_contDiffOn (p q : M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hsupport : tsupport φ ⊆ (chartAt E q).source) :
    ContDiffOn ℝ ∞ (chartWeightDensity p q φ) (chartAt E p).target := by
  intro z hz
  let e : OpenPartialHomeomorph M E := chartAt E p
  by_cases hzU : z ∈ chartTransitionDomain p q
  · have hpull : ContDiffOn ℝ ∞ (φ ∘ e.symm) (chartTransition p q).source :=
      (TensorProbeNative.contDiffOn_scalar_chartInverse p hφ).mono inter_subset_left
    have hproduct := hpull.mul (chartTransitionJacobian_contDiffOn p q)
    have heq : chartWeightDensity p q φ =ᶠ[𝓝 z]
        (fun y => φ (e.symm y) * chartTransitionJacobian p q y) := by
      filter_upwards [(chartTransition p q).open_source.mem_nhds hzU] with y hy
      exact chartWeightDensity_of_mem p q φ hy
    exact ((hproduct.contDiffAt ((chartTransition p q).open_source.mem_nhds hzU)).congr_of_eventuallyEq
      heq).contDiffWithinAt
  · have hxq : e.symm z ∉ (chartAt E q).source := fun hxq => hzU ⟨hz, hxq⟩
    have hxsupport : e.symm z ∉ tsupport φ := fun hx => hxq (hsupport hx)
    have hzero : (fun y => φ (e.symm y)) =ᶠ[𝓝 z] 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hxsupport).comp_tendsto
        (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hz)).tendsto
    have heq : chartWeightDensity p q φ =ᶠ[𝓝 z] 0 := by
      filter_upwards [hzero] with y hy
      by_cases hyU : y ∈ chartTransitionDomain p q
      · rw [chartWeightDensity_of_mem p q φ hyU]
        change φ (e.symm y) = 0 at hy
        rw [hy, zero_mul, Pi.zero_apply]
      · exact chartWeightDensity_of_notMem p q φ hyU
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq heq).contDiffWithinAt

namespace FiniteChartData

variable (d : FiniteChartData (n := n) (M := M))


def chartDensity (p : M) (z : E) : ℝ :=
  ∑ i : d.centers, chartWeightDensity p i.val (d.weight i) z

theorem chartDensity_nonneg (p : M) (z : E) : 0 ≤ d.chartDensity p z :=
  Finset.sum_nonneg (fun i _ => chartWeightDensity_nonneg p i.val (d.weight_nonneg i) z)

theorem chartDensity_pos (p : M) {z : E} (hz : z ∈ (chartAt E p).target) :
    0 < d.chartDensity p z := by
  classical
  obtain ⟨i, hi⟩ := d.exists_weight_pos ((chartAt E p).symm z)
  exact (chartWeightDensity_pos_of_weight_pos p i.val (d.weight_support_subset i) hz hi).trans_le
    (Finset.single_le_sum
      (fun j _ => chartWeightDensity_nonneg p j.val (d.weight_nonneg j) z) (Finset.mem_univ i))

theorem chartDensity_contDiffOn (p : M) :
    ContDiffOn ℝ ∞ (d.chartDensity p) (chartAt E p).target :=
  ContDiffOn.sum (fun i _ => chartWeightDensity_contDiffOn p i.val
    (d.weight_smooth i) (d.weight_support_subset i))

theorem chartDensity_inv_contDiffOn (p : M) :
    ContDiffOn ℝ ∞ (fun z => (d.chartDensity p z)⁻¹) (chartAt E p).target :=
  (d.chartDensity_contDiffOn p).inv (fun z hz => (d.chartDensity_pos p hz).ne')

end FiniteChartData

end PoincareConjecture.ChartMeasureNative
