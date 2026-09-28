import PoincareConjecture.Proofs.M10.ChartWeakComparison
import PoincareConjecture.Proofs.M10.WeakChartData
import PoincareConjecture.Proofs.M10.WeakRegularIdentities
import PoincareConjecture.Proofs.M10.TimeDerivativeMeasurable
import PoincareConjecture.Proofs.M10.WeakPartition
import PoincareConjecture.Proofs.M10.MeasureRegularity











set_option autoImplicit false

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_weak_inequalities
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (p : M) (τ : ℝ)
    (hτ : 0 < τ) (hmax : τ < τmax) (φ : M → ℝ)
    (hφ : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ φ) (hc : HasCompactSupport φ)
    (hpos : ∀ q, 0 ≤ φ q) :
    Integrable (reducedLengthFirstWeakIntegrand F T p τ φ)
      (calibratedMetricVolume (F.metric (T - τ))) ∧
    Integrable (reducedLengthSecondWeakIntegrand F T p τ φ)
      (calibratedMetricVolume (F.metric (T - τ))) ∧
    0 ≤ ∫ q, reducedLengthFirstWeakIntegrand F T p τ φ q
      ∂calibratedMetricVolume (F.metric (T - τ)) ∧
    (∫ q, reducedLengthSecondWeakIntegrand F T p τ φ q
      ∂calibratedMetricVolume (F.metric (T - τ))) ≤ 0 := by
  obtain ⟨R⟩ := reducedLength_measure_regularity hL hDifferential hwindow p
  let g := F.metric (T - τ)
  let D := F.connection (T - τ)
  let μ := calibratedMetricVolume g
  let u := fun q ↦ reducedLength F T p q τ
  let H := fun q ↦ -deriv (fun s ↦ reducedLength F T p q s) τ +
    ((n : ℝ) / 2 - u q) / τ
  have hreg : ∀ᵐ q ∂μ, (q, τ) ∈ R.regularDomain :=
    ae_iff.mpr (R.slice_complement_null τ hτ hmax)
  have hu : Continuous u := R.continuous.comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨mem_univ _, hτ, hmax⟩)
  have hH : Measurable H := reducedLength_weak_bound_measurable hL hDifferential hτ hmax
  have hlocal : ∀ q₀ : M, ∃ U : Set M, IsOpen U ∧ q₀ ∈ U ∧
      ∀ ψ : M → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U → (∀ q, 0 ≤ ψ q) →
        Integrable (fun q ↦ ψ q * H q - u q * D.laplacian ψ q) μ ∧
        0 ≤ ∫ q, ψ q * H q - u q * D.laplacian ψ q ∂μ := by
    intro q₀
    obtain ⟨r, K, S, A, hr, hK, hS, hA, htarget, hconc, hcoeff, hbound⟩ :=
      reducedLength_weak_chart_data hL hDifferential p q₀ R hτ hmax
    let e := extChartAt (𝓡 n) q₀
    let U := e.source ∩ e ⁻¹' ball (e q₀) r
    refine ⟨U, (continuousOn_extChartAt (I := 𝓡 n) q₀).isOpen_inter_preimage
      (isOpen_extChartAt_source q₀) isOpen_ball,
      ⟨mem_extChartAt_source q₀, mem_ball_self hr⟩, ?_⟩
    intro ψ hψ hψc hψs hψpos
    apply calibrated_weak_comparison_in_chart g D q₀ hu hH hr hK hS hA
      htarget hconc hcoeff ?_ ?_ hψ hψc hψs hψpos
    · filter_upwards [hreg] with q hq
      obtain ⟨w⟩ := R.regular_points (q, τ) hq
      exact ⟨(reducedLength_space_contMDiffAt w).of_le (by decide : (2 : ℕ∞ω) ≤ ∞),
        reducedLength_regular_laplacian_le hDifferential w⟩
    · filter_upwards [hreg] with q hq hqs hqb
      have h := hbound (extChartAt (𝓡 n) q₀ q) hqb
      simpa only [(extChartAt (𝓡 n) q₀).left_inv hqs] using h
        (by simpa only [(extChartAt (𝓡 n) q₀).left_inv hqs] using hq)
  have hweak := weak_comparison_of_local D μ u H hlocal φ hφ hc hpos
  have heq : reducedLengthFirstWeakIntegrand F T p τ φ =ᵐ[μ]
      (fun q ↦ φ q * H q - u q * D.laplacian φ q) ∧
      reducedLengthSecondWeakIntegrand F T p τ φ =ᵐ[μ]
      (fun q ↦ -2 * (φ q * H q - u q * D.laplacian φ q)) := by
    constructor
    · filter_upwards [hreg] with q hq
      obtain ⟨w⟩ := R.regular_points (q, τ) hq
      exact (reducedLength_regular_weak_integrands hDifferential w φ).1
    · filter_upwards [hreg] with q hq
      obtain ⟨w⟩ := R.regular_points (q, τ) hq
      exact (reducedLength_regular_weak_integrands hDifferential w φ).2
  refine ⟨hweak.1.congr heq.1.symm, (hweak.1.const_mul (-2)).congr heq.2.symm, ?_, ?_⟩
  · rw [integral_congr_ae heq.1]
    exact hweak.2
  · rw [integral_congr_ae heq.2, integral_const_mul]
    nlinarith [hweak.2]

end PoincareConjecture.M10
