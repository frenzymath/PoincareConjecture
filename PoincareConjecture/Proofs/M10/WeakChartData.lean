import PoincareConjecture.Proofs.M10.ReducedLengthSemiconcavity
import PoincareConjecture.Proofs.M10.ChartOperatorBounds
import PoincareConjecture.Definitions.Ch06.ReducedVolume









set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

noncomputable local instance weakChartBilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance weakChartBilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_weak_chart_data
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (p q₀ : M) (R : ReducedLengthMeasureData F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    let e := extChartAt (𝓡 n) q₀
    let B := pullbackMetricForm (F.metric (T - τ)) e.symm
    let ρ := pullbackJacobian (F.metric (T - τ)) e.symm
    let u := fun y ↦ reducedLength F T p (e.symm y) τ
    let H := fun q ↦ -deriv (fun s ↦ reducedLength F T p q s) τ +
      ((n : ℝ) / 2 - reducedLength F T p q τ) / τ
    ∃ r K S A : ℝ, 0 < r ∧ 0 ≤ K ∧ 0 ≤ S ∧ 0 ≤ A ∧
      ball (e q₀) (4 * r) ⊆ e.target ∧
      ConcaveOn ℝ (ball (e q₀) (4 * r)) (fun y ↦ u y - K * ‖y‖ ^ 2 / 2) ∧
      (∀ y ∈ ball (e q₀) (4 * r), ‖fderiv ℝ B y‖ ≤ S ∧ ‖(B y).inverse‖ ≤ S ∧
        ρ y ≤ S ∧ ‖fderiv ℝ ρ y‖ ≤ S) ∧
      (∀ y ∈ ball (e q₀) (4 * r), (e.symm y, τ) ∈ R.regularDomain → |H (e.symm y)| ≤ A) := by
  let e := extChartAt (𝓡 n) q₀
  let u := fun y ↦ reducedLength F T p (e.symm y) τ
  obtain ⟨r₀, hr₀, htarget, K, hK, hconc⟩ :=
    reducedLength_chart_semiconcave hL hDifferential p q₀ hτ hmax
  obtain ⟨S, hS, hmetric⟩ := chartOperator_eventually_bounded (F.metric (T - τ)) q₀
  obtain ⟨N, hN, hqN, _, C, hC, hderiv⟩ :=
    R.local_derivative_bounds (q₀, τ) ⟨mem_univ _, hτ, hmax⟩
  have hN' : ∀ᶠ y in 𝓝 (e q₀), (e.symm y, τ) ∈ N := by
    have ht := (continuousAt_extChartAt_symm (I := 𝓡 n) q₀).prodMk
      (continuousAt_const (y := τ))
    exact ht (hN.mem_nhds (by simpa only [e, extChartAt_to_inv] using hqN))
  have hu : Continuous (fun q ↦ reducedLength F T p q τ) :=
    R.continuous.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ ↦ ⟨mem_univ _, hτ, hmax⟩)
  have huc : ContinuousAt u (e q₀) :=
    hu.continuousAt.comp (continuousAt_extChartAt_symm (I := 𝓡 n) q₀)
  let L := |u (e q₀)| + 1
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hub : ∀ᶠ y in 𝓝 (e q₀), |u y| < L := huc.abs (eventually_lt_nhds (lt_add_one _))
  have hnear : ∀ᶠ y in 𝓝 (e q₀), y ∈ ball (e q₀) r₀ ∧
      (y ∈ e.target ∧
        ‖fderiv ℝ (pullbackMetricForm (F.metric (T - τ)) e.symm) y‖ ≤ S ∧
        ‖(pullbackMetricForm (F.metric (T - τ)) e.symm y).inverse‖ ≤ S ∧
        pullbackJacobian (F.metric (T - τ)) e.symm y ≤ S ∧
        ‖fderiv ℝ (pullbackJacobian (F.metric (T - τ)) e.symm) y‖ ≤ S) ∧
      (e.symm y, τ) ∈ N ∧ |u y| < L := by
    filter_upwards [ball_mem_nhds (e q₀) hr₀, hmetric, hN', hub] with y hy hm hn hl
    exact ⟨hy, hm, hn, hl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := δ / 4
  have h4r : 4 * r = δ := by dsimp only [r]; ring
  let A := C + ((n : ℝ) / 2 + L) / τ
  refine ⟨r, K, S, A, by dsimp only [r]; positivity, hK, hS,
    by dsimp only [A]; positivity, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [h4r] at hy
    exact (hball hy).2.1.1
  · apply hconc.subset _ (convex_ball _ _)
    intro y hy
    rw [h4r] at hy
    exact (hball hy).1
  · intro y hy
    rw [h4r] at hy
    exact (hball hy).2.1.2
  · intro y hy hreg
    rw [h4r] at hy
    obtain ⟨_, _, hyN, hyL⟩ := hball hy
    have hd := (hderiv (e.symm y, τ) ⟨hyN, hreg⟩).1
    have hval : |(n : ℝ) / 2 - u y| ≤ (n : ℝ) / 2 + L :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / 2)]; linarith)
    calc
      _ ≤ |deriv (fun s ↦ reducedLength F T p (e.symm y) s) τ| +
          |((n : ℝ) / 2 - u y) / τ| := by
        simpa only [abs_neg] using abs_add_le
          (-deriv (fun s ↦ reducedLength F T p (e.symm y) s) τ)
          (((n : ℝ) / 2 - u y) / τ)
      _ ≤ C + ((n : ℝ) / 2 + L) / τ := by
        rw [abs_div, abs_of_pos hτ]
        exact add_le_add hd (div_le_div_of_nonneg_right hval hτ.le)

end PoincareConjecture.M10
