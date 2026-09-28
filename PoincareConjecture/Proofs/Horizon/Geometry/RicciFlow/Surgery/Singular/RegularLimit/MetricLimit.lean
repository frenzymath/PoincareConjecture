import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison.LocalCurvature
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

noncomputable section

namespace PoincareConjecture

namespace RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a s T K : ℝ} (F : RicciFlow n M (Ico a T))

theorem metric_diagonal_bounds_on_tail (has : a ≤ s) (hsT : s < T)
    (hK : 0 ≤ K) (x : M)
    (hRm : ∀ t ∈ Ico s T, (F.connection t).curvatureTensorNorm x ≤ K)
    (v : TangentSpace (𝓡 n) x) {t : ℝ} (ht : t ∈ Ico s T) :
    Real.exp (-2 * (n : ℝ) * K * (T - s)) * (F.metric s).inner x v v ≤
        (F.metric t).inner x v v ∧
      (F.metric t).inner x v v ≤
        Real.exp (2 * (n : ℝ) * K * (T - s)) * (F.metric s).inner x v v := by
  have h := metric_comparison_at_of_curvature_bound F ⟨has, hsT⟩
    ⟨has.trans ht.1, ht.2⟩ ht.1 hK x
    (fun τ hτ => hRm τ ⟨hτ.1, hτ.2.trans_lt ht.2⟩) v
  have hq : 0 ≤ (F.metric s).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((F.metric s).pos x v hv).le
  have hc : 0 ≤ 2 * (n : ℝ) * K := by positivity
  constructor
  · apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hq) h.1
    nlinarith [mul_le_mul_of_nonneg_left ht.2.le hc]
  · apply le_trans h.2 (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hq)
    nlinarith [mul_le_mul_of_nonneg_left ht.2.le hc]

theorem exists_terminal_metric_diagonal (has : a ≤ s) (hsT : s < T)
    (hK : 0 ≤ K) (x : M)
    (hRm : ∀ t ∈ Ico s T, (F.connection t).curvatureTensorNorm x ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    ∃ l : ℝ, Tendsto (fun t => (F.metric t).inner x v v) (𝓝[<] T) (𝓝 l) ∧
      Real.exp (-2 * (n : ℝ) * K * (T - s)) * (F.metric s).inner x v v ≤ l := by
  let q : ℝ → ℝ := fun t => (F.metric t).inner x v v
  let B := Real.exp (2 * (n : ℝ) * K * (T - s)) * q s
  have hq (t : ℝ) : 0 ≤ q t := by
    by_cases hv : v = 0
    · simp [q, hv]
    · exact ((F.metric t).pos x v hv).le
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (hq s)
  let L : ℝ≥0 := ⟨2 * (n : ℝ) * K * B, by positivity⟩
  have hbound (t : ℝ) (ht : t ∈ Ico s T) :
      ‖-2 * (F.connection t).ricci x v v‖₊ ≤ L := by
    change |(-2 : ℝ) * (F.connection t).ricci x v v| ≤ 2 * (n : ℝ) * K * B
    rw [abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have h := abs_ricci_le_curvatureTensorNorm (F.connection t) x v
    have hupper := (metric_diagonal_bounds_on_tail F has hsT hK x hRm v ht).2
    have hcurv := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hRm t ht) (Nat.cast_nonneg n)) (hq t)
    have htime := mul_le_mul_of_nonneg_left hupper
      (mul_nonneg (Nat.cast_nonneg n) hK)
    dsimp only [B, q] at *
    nlinarith
  have hderiv (t : ℝ) (ht : t ∈ Ico s T) :
      HasDerivWithinAt q (-2 * (F.connection t).ricci x v v) (Ico s T) t :=
    (F.equation t ⟨has.trans ht.1, ht.2⟩ x v v).mono
      (fun _ hτ => ⟨has.trans hτ.1, hτ.2⟩)
  have hLip : LipschitzOnWith L q (Ico s T) :=
    (convex_Ico s T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hderiv hbound
  obtain ⟨qbar, hqbar, heq⟩ := hLip.extend_real
  have hlimit : Tendsto q (𝓝[<] T) (𝓝 (qbar T)) :=
    (hqbar.continuous.tendsto T).mono_left nhdsWithin_le_nhds |>.congr'
      (by filter_upwards [Ico_mem_nhdsLT hsT] with t ht using (heq ht).symm)
  refine ⟨qbar T, hlimit, le_of_tendsto_of_tendsto tendsto_const_nhds hlimit ?_⟩
  filter_upwards [Ico_mem_nhdsLT hsT] with t ht
  exact (metric_diagonal_bounds_on_tail F has hsT hK x hRm v ht).1

theorem exists_terminal_metric_coefficient (has : a ≤ s) (hsT : s < T)
    (hK : 0 ≤ K) (x : M)
    (hRm : ∀ t ∈ Ico s T, (F.connection t).curvatureTensorNorm x ≤ K)
    (v w : TangentSpace (𝓡 n) x) :
    ∃ l : ℝ, Tendsto (fun t => (F.metric t).inner x v w) (𝓝[<] T) (𝓝 l) := by
  obtain ⟨ladd, hadd, _⟩ := exists_terminal_metric_diagonal F has hsT hK x hRm (v + w)
  obtain ⟨lv, hv, _⟩ := exists_terminal_metric_diagonal F has hsT hK x hRm v
  obtain ⟨lw, hw, _⟩ := exists_terminal_metric_diagonal F has hsT hK x hRm w
  refine ⟨(ladd - lv - lw) / 2, ?_⟩
  convert ((hadd.sub hv).sub hw).div_const 2 using 1
  ext t
  simp only [map_add, add_apply]
  rw [(F.metric t).symm x w v]
  ring

end RicciFlowAnalysis

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_terminal_metric_coefficient (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v w : TangentSpace (𝓡 3) x) :
    ∃ l : ℝ, Tendsto (fun t => (H.reference.flow.metric t).inner x v w)
      (𝓝[<] T) (𝓝 l) := by
  obtain ⟨s, K, U, hs, hsT, hK, _, hxU, _, hbound⟩ :=
    H.exists_open_uniform_curvature_tail P04 hx
  exact RicciFlowAnalysis.exists_terminal_metric_coefficient H.reference.flow hs.le hsT hK.le x
    (fun t ht => hbound t ht x hxU) v w

theorem exists_positive_terminal_metric_diagonal (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0) :
    ∃ l : ℝ, 0 < l ∧ Tendsto (fun t => (H.reference.flow.metric t).inner x v v)
      (𝓝[<] T) (𝓝 l) := by
  obtain ⟨s, K, U, hs, hsT, hK, _, hxU, _, hbound⟩ :=
    H.exists_open_uniform_curvature_tail P04 hx
  obtain ⟨l, hl, hlower⟩ := RicciFlowAnalysis.exists_terminal_metric_diagonal H.reference.flow
    hs.le hsT hK.le x (fun t ht => hbound t ht x hxU) v
  exact ⟨l, lt_of_lt_of_le (mul_pos (Real.exp_pos _)
    ((H.reference.flow.metric s).pos x v hv)) hlower, hl⟩

noncomputable def terminalMetricCoefficient (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v w : TangentSpace (𝓡 3) x) : ℝ :=
  Classical.choose (H.exists_terminal_metric_coefficient P04 hx v w)

theorem tendsto_terminalMetricCoefficient (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v w : TangentSpace (𝓡 3) x) :
    Tendsto (fun t => (H.reference.flow.metric t).inner x v w) (𝓝[<] T)
      (𝓝 (H.terminalMetricCoefficient P04 hx v w)) :=
  Classical.choose_spec (H.exists_terminal_metric_coefficient P04 hx v w)

theorem terminalMetricCoefficient_add_left (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (u v w : TangentSpace (𝓡 3) x) :
    H.terminalMetricCoefficient P04 hx (u + v) w =
      H.terminalMetricCoefficient P04 hx u w + H.terminalMetricCoefficient P04 hx v w := by
  apply tendsto_nhds_unique (H.tendsto_terminalMetricCoefficient P04 hx (u + v) w)
  simpa only [map_add, add_apply] using
    (H.tendsto_terminalMetricCoefficient P04 hx u w).add
      (H.tendsto_terminalMetricCoefficient P04 hx v w)

theorem terminalMetricCoefficient_smul_left (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (c : ℝ) (v w : TangentSpace (𝓡 3) x) :
    H.terminalMetricCoefficient P04 hx (c • v) w =
      c * H.terminalMetricCoefficient P04 hx v w := by
  apply tendsto_nhds_unique (H.tendsto_terminalMetricCoefficient P04 hx (c • v) w)
  simpa only [map_smul, smul_apply, smul_eq_mul] using
    (H.tendsto_terminalMetricCoefficient P04 hx v w).const_mul c

theorem terminalMetricCoefficient_symm (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v w : TangentSpace (𝓡 3) x) :
    H.terminalMetricCoefficient P04 hx v w = H.terminalMetricCoefficient P04 hx w v := by
  apply tendsto_nhds_unique (H.tendsto_terminalMetricCoefficient P04 hx v w)
  simpa only [(H.reference.flow.metric _).symm x w v] using
    H.tendsto_terminalMetricCoefficient P04 hx w v

noncomputable def terminalMetricBilinear (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  exact LinearMap.toContinuousLinearMap {
    toFun := fun v => LinearMap.toContinuousLinearMap {
      toFun := fun w => H.terminalMetricCoefficient P04 hx v w
      map_add' := fun u w => by
        rw [H.terminalMetricCoefficient_symm P04 hx v (u + w),
          H.terminalMetricCoefficient_add_left,
          H.terminalMetricCoefficient_symm P04 hx u v,
          H.terminalMetricCoefficient_symm P04 hx w v]
      map_smul' := fun c w => by
        rw [H.terminalMetricCoefficient_symm P04 hx v (c • w),
          H.terminalMetricCoefficient_smul_left,
          H.terminalMetricCoefficient_symm P04 hx w v]
        rfl }
    map_add' := fun u v => by
      apply ContinuousLinearMap.ext
      intro w
      exact H.terminalMetricCoefficient_add_left P04 hx u v w
    map_smul' := fun c v => by
      apply ContinuousLinearMap.ext
      intro w
      exact H.terminalMetricCoefficient_smul_left P04 hx c v w }

theorem terminalMetricBilinear_symm (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v w : TangentSpace (𝓡 3) x) :
    H.terminalMetricBilinear P04 hx v w = H.terminalMetricBilinear P04 hx w v :=
  H.terminalMetricCoefficient_symm P04 hx v w

theorem terminalMetricBilinear_pos (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0) :
    0 < H.terminalMetricBilinear P04 hx v v := by
  obtain ⟨l, hl, hlimit⟩ := H.exists_positive_terminal_metric_diagonal P04 hx v hv
  change 0 < H.terminalMetricCoefficient P04 hx v v
  rw [tendsto_nhds_unique (H.tendsto_terminalMetricCoefficient P04 hx v v) hlimit]
  exact hl

theorem tendsto_terminalMetricBilinear_apply (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    (v w : TangentSpace (𝓡 3) x) :
    Tendsto (fun t => (H.reference.flow.metric t).inner x v w) (𝓝[<] T)
      (𝓝 (H.terminalMetricBilinear P04 hx v w)) :=
  H.tendsto_terminalMetricCoefficient P04 hx v w

theorem terminalMetricBilinear_bounds (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet)
    {s K : ℝ} (hs : H.reference.tMinus ≤ s) (hsT : s < T) (hK : 0 ≤ K)
    (hRm : ∀ t ∈ Ico s T, (H.reference.flow.connection t).curvatureTensorNorm x ≤ K)
    (v : TangentSpace (𝓡 3) x) :
    Real.exp (-2 * (3 : ℝ) * K * (T - s)) * (H.reference.flow.metric s).inner x v v ≤
        H.terminalMetricBilinear P04 hx v v ∧
      H.terminalMetricBilinear P04 hx v v ≤
        Real.exp (2 * (3 : ℝ) * K * (T - s)) *
          (H.reference.flow.metric s).inner x v v := by
  have hlimit := H.tendsto_terminalMetricBilinear_apply P04 hx v v
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
    filter_upwards [Ico_mem_nhdsLT hsT] with t ht
    exact (RicciFlowAnalysis.metric_diagonal_bounds_on_tail
      H.reference.flow hs hsT hK x hRm v ht).1
  · apply le_of_tendsto hlimit
    filter_upwards [Ico_mem_nhdsLT hsT] with t ht
    exact (RicciFlowAnalysis.metric_diagonal_bounds_on_tail
      H.reference.flow hs hsT hK x hRm v ht).2

theorem tendsto_terminalMetricBilinear (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    Tendsto (fun t => (H.reference.flow.metric t).inner x) (𝓝[<] T)
      (𝓝 (H.terminalMetricBilinear P04 hx)) := by
  let : NormedAddCommGroup (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  let : NormedSpace ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  let G : ℝ → TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ :=
    fun t => if t < T then (H.reference.flow.metric t).inner x
      else H.terminalMetricBilinear P04 hx
  have hG : ContinuousWithinAt G (Iio T) T := by
    apply continuousWithinAt_clm_apply.mpr
    intro v
    apply continuousWithinAt_clm_apply.mpr
    intro w
    change Tendsto (fun t => G t v w) (𝓝[<] T) (𝓝 (G T v w))
    have hGT : G T = H.terminalMetricBilinear P04 hx := by simp [G]
    rw [hGT]
    apply (H.tendsto_terminalMetricBilinear_apply P04 hx v w).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [G, mem_Iio.mp ht, ↓reduceIte]
  have hGT : G T = H.terminalMetricBilinear P04 hx := by simp [G]
  rw [ContinuousWithinAt, hGT] at hG
  apply hG.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [G, mem_Iio.mp ht, ↓reduceIte]

end SingularTimeAssumptions

end PoincareConjecture
