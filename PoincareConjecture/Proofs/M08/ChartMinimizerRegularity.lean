import PoincareConjecture.Proofs.M08.ChartCoefficients
import PoincareConjecture.Proofs.M08.ChartPerturbation
import PoincareConjecture.Proofs.M08.ChartStationarity
import PoincareConjecture.Proofs.M08.WeakVelocity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe uM

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type uM} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def IsChartH1Minimizer {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (a b : ℝ) (γ : ℝ → M) (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b) : Prop :=
  ∀ (ξ : ℝ → M), ContinuousOn ξ (Icc a b) → ξ a = γ a → ξ b = γ b →
    MapsTo ξ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source →
    ∀ v : ChartL2 (EuclideanSpace ℝ (Fin n)) a b,
      (∀ s ∈ Icc a b, extChartAt (𝓡 n) x (ξ s) = extChartAt (𝓡 n) x (ξ a) +
        ∫ r in a..s, v r) →
      chartH1Action F T x a b γ w ≤ chartH1Action F T x a b ξ v

set_option maxHeartbeats 800000 in

theorem chart_minimum_affine_stationary {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{uM}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (x : M) (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ interior J)
    (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hw : ∀ s ∈ Icc a b, extChartAt (𝓡 n) x (γ s) =
      extChartAt (𝓡 n) x (γ a) + ∫ r in a..s, w r)
    (hmin : IsChartH1Minimizer F T x a b γ w)
    (η ν : ℝ → EuclideanSpace ℝ (Fin n))
    (hη : ContinuousOn η (Icc a b)) (hν : ContinuousOn ν (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt η (ν s) s)
    (hηa : η a = 0) (hηb : η b = 0) :
    (∫ s in a..b,
      spatialFDeriv (chartActionMetric F T x) (s, extChartAt (𝓡 n) x (γ s))
          (η s) (w s) (w s) / 2 +
        chartActionMetric F T x (s, extChartAt (𝓡 n) x (γ s)) (w s) (ν s) +
        spatialFDeriv (chartActionPotential F T x) (s, extChartAt (𝓡 n) x (γ s)) (η s)) = 0 := by
  let e := extChartAt (𝓡 n) x
  let u : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have hu : ContinuousOn u (Icc a b) :=
    (continuousOn_extChartAt (I := 𝓡 n) x).comp hγ hsrc'
  obtain ⟨K, hK, hKt, huK, δ, hδ, hδ1, hδK⟩ :=
    exists_chart_affine_buffer x γ hγ hsrc η hη
  obtain ⟨C, hC, hcoeff⟩ := chart_spatial_coefficient_bounds F hM04 T x K hK hKt htime
  obtain ⟨D₁, hD₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hη
  obtain ⟨D₂, hD₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hν
  let D := |D₁| + |D₂|
  have hD : 0 ≤ D := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hdir : ∀ s ∈ Icc a b, ‖η s‖ ≤ D ∧ ‖ν s‖ ≤ D := by
    intro s hs
    have h₁ := hD₁ s hs
    have h₂ := hD₂ s hs
    dsimp only [D]
    constructor <;> linarith [le_abs_self D₁, le_abs_self D₂, abs_nonneg D₁, abs_nonneg D₂]
  have hsub : Icc a b ×ˢ K ⊆ chartActionDomain F T x :=
    fun z hz ↦ ⟨htime z.1 hz.1, hKt hz.2⟩
  have hG := chartActionMetric_contDiffOn F T x
  have hV := chartActionPotential_contDiffOn F hM04 T x
  have hDG := spatialFDeriv_continuousOn (chartActionDomain_open F T x) _ hG
  have hDV := spatialFDeriv_continuousOn (chartActionDomain_open F T x) _ hV
  let f : ℝ → ℝ := fun ε ↦ ∫ s in a..b,
    chartActionMetric F T x (s, u s + ε • η s) (w s + ε • ν s) (w s + ε • ν s) / 2 +
      chartActionPotential F T x (s, u s + ε • η s)
  have hf := (affine_chart_action_hasDerivAt hab.le hδ hδ1 hC hD K u w η ν hu
    (Lp.memLp w) hη hν
    (fun s v ↦ chartActionMetric F T x (s, v))
    (fun s v ↦ chartActionPotential F T x (s, v))
    (fun s v ↦ spatialFDeriv (chartActionMetric F T x) (s, v))
    (fun s v ↦ spatialFDeriv (chartActionPotential F T x) (s, v))
    (hG.continuousOn.mono hsub) (hV.continuousOn.mono hsub)
    (hDG.mono hsub) (hDV.mono hsub)
    (fun ε hε s hs ↦ hδK ε (abs_lt.mpr hε) hs)
    (fun s hs v hv ↦ hasFDerivAt_spatial (chartActionDomain_open F T x) _ hG
      (hsub ⟨hs, hv⟩))
    (fun s hs v hv ↦ hasFDerivAt_spatial (chartActionDomain_open F T x) _ hV
      (hsub ⟨hs, hv⟩))
    (fun s hs v hv ↦ chartActionMetric_symm F T x (hsub ⟨hs, hv⟩))
    hcoeff hdir).2
  have hνLp : MemLp ν 2 (volume.restrict (Icc a b)) :=
    (continuousOn_memLp_top_Icc hν).mono_exponent le_top
  have hbase : chartH1Action F T x a b γ w = f 0 := by
    have h := chartH1Action_eq_coordinate_integral F hM04 T hab.le x γ hγ hsrc
      (fun s hs ↦ interior_subset (htime s hs)) u
      (fun s hs ↦ (e.left_inv (hsrc' hs)).symm) w w Filter.EventuallyEq.rfl
    simpa only [f, zero_smul, add_zero] using h
  have hlocal : IsLocalMin f 0 := by
    have hnhds : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ
    filter_upwards [hnhds] with ε hε
    have htarget : MapsTo (fun s ↦ e (γ s) + ε • η s) (Icc a b) e.target :=
      fun s hs ↦ hKt (hδK ε (abs_lt.mpr hε) hs)
    obtain ⟨ξ, v, hξ, hξa, hξb, hξsrc, hξdef, hv, _, hvprimitive⟩ :=
      chart_affine_competitor hab.le x γ hγ hsrc w hw η ν hη hd hνLp hηa hηb ε htarget
    have haction := chartH1Action_eq_coordinate_integral F hM04 T hab.le x ξ hξ hξsrc
      (fun s hs ↦ interior_subset (htime s hs)) (fun s ↦ u s + ε • η s)
      (fun s _ ↦ hξdef s) v (fun s ↦ w s + ε • ν s) hv
    change chartH1Action F T x a b ξ v = f ε at haction
    rw [← hbase, ← haction]
    exact hmin ξ hξ hξa hξb hξsrc v hvprimitive
  exact hlocal.hasDerivAt_eq_zero hf

set_option maxHeartbeats 800000 in

theorem chart_minimum_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{uM}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (x : M) (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ interior J)
    (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hw : ∀ s ∈ Icc a b, extChartAt (𝓡 n) x (γ s) =
      extChartAt (𝓡 n) x (γ a) + ∫ r in a..s, w r)
    (hmin : IsChartH1Minimizer F T x a b γ w) :
    ContDiffOn ℝ 1 ((extChartAt (𝓡 n) x) ∘ γ) (Icc a b) := by
  let e := extChartAt (𝓡 n) x
  let u : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have hu : ContinuousOn u (Icc a b) :=
    (continuousOn_extChartAt (I := 𝓡 n) x).comp hγ hsrc'
  have hpair : ContinuousOn (fun s ↦ (s, u s)) (Icc a b) := continuousOn_id.prodMk hu
  have hdom : MapsTo (fun s ↦ (s, u s)) (Icc a b) (chartActionDomain F T x) :=
    fun s hs ↦ ⟨htime s hs, e.map_source (hsrc' hs)⟩
  let G := fun s ↦ chartActionMetric F T x (s, u s)
  let DG := fun s ↦ spatialFDeriv (chartActionMetric F T x) (s, u s)
  let DV := fun s ↦ spatialFDeriv (chartActionPotential F T x) (s, u s)
  have hG : ContinuousOn G (Icc a b) :=
    (chartActionMetric_contDiffOn F T x).continuousOn.comp hpair hdom
  have hDG : ContinuousOn DG (Icc a b) :=
    (spatialFDeriv_continuousOn (chartActionDomain_open F T x) _
      (chartActionMetric_contDiffOn F T x)).comp hpair hdom
  have hDV : ContinuousOn DV (Icc a b) :=
    (spatialFDeriv_continuousOn (chartActionDomain_open F T x) _
      (chartActionPotential_contDiffOn F hM04 T x)).comp hpair hdom
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hDG
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hDV
  let C := |C₀| + |C₁| + |C₂|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ s ∈ Icc a b, ‖G s‖ ≤ C ∧ ‖DG s‖ ≤ C ∧ ‖DV s‖ ≤ C := by
    intro s hs
    have h₀ := hC₀ s hs
    have h₁ := hC₁ s hs
    have h₂ := hC₂ s hs
    dsimp only [C]
    refine ⟨?_, ?_, ?_⟩ <;>
      linarith [le_abs_self C₀, le_abs_self C₁, le_abs_self C₂,
        abs_nonneg C₀, abs_nonneg C₁, abs_nonneg C₂]
  let A := fun s ↦ chartMetricOperator F T x (s, u s)
  let B := fun s ↦ Ring.inverse (A s)
  let Q := fun s ↦ chartForceVector (DG s) (DV s) (w s)
  have hA : ContinuousOn A (Icc a b) :=
    (chartMetricOperator_contDiffOn F T x).continuousOn.comp hpair hdom
  have hB : ContinuousOn B (Icc a b) :=
    (chartMetricInverse_contDiffOn F T x).continuousOn.comp hpair hdom
  have hinv : ∀ s ∈ Icc a b, ∀ v : EuclideanSpace ℝ (Fin n), B s (A s v) = v :=
    fun s hs v ↦ inverse_operator_apply _ (chartMetricOperator_isUnit F T x (hdom hs)) v
  have hmomentum (s : ℝ) : A s (w s) = chartMomentumVector (G s) (w s) := rfl
  obtain ⟨hP, hQ⟩ := chart_momentum_force_intervalIntegrable hab.le hC w (Lp.memLp w)
    G DG DV hG hDG hDV hbound
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • A s (w s)) =
        -(∫ s in a..b, φ s • Q s) := by
    intro φ hφ _ hφsupp
    have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
      (fun ha ↦ (lt_irrefl a) (hφsupp ha).1)
    have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
      (fun hb ↦ (lt_irrefl b) (hφsupp hb).2)
    have hstationary (z : EuclideanSpace ℝ (Fin n)) :
        (∫ s in a..b, DG s (φ s • z) (w s) (w s) / 2 +
          G s (w s) (deriv φ s • z) + DV s (φ s • z)) = 0 := by
      apply chart_minimum_affine_stationary F hM04 T hab x γ hγ hsrc htime w hw hmin
        (fun s ↦ φ s • z) (fun s ↦ deriv φ s • z)
        (hφ.continuous.continuousOn.smul continuousOn_const)
        ((hφ.continuous_deriv (by simp)).continuousOn.smul continuousOn_const)
      · intro s _
        exact ((hφ.differentiable (by simp)) s).hasDerivAt.smul_const z
      · simp only [hφa, zero_smul]
      · simp only [hφb, zero_smul]
    exact (weak_momentum_of_chart_stationarity hab.le hC w (Lp.memLp w)
      G DG DV hG hDG hDV hbound φ hφ hstationary).2.2
  obtain ⟨c, q, _, _, _, _, _, _, hreg⟩ := weak_velocity_regular hab u w hw A B hA hB hinv
    Q hQ hP hweak
  exact hreg

end PoincareConjecture.M08
