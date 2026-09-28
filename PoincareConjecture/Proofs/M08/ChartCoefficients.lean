import PoincareConjecture.Proofs.M08.ChartRegularity
import PoincareConjecture.Proofs.M08.LocalMinimality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.M08

section Derivative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def spatialFDeriv (f : ℝ × E → H) (z : ℝ × E) : E →L[ℝ] H :=
  (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E)

theorem spatialFDeriv_continuousOn {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContinuousOn (spatialFDeriv f) Ω :=
  (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_comp continuousOn_const

theorem hasFDerivAt_spatial {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f Ω) {s : ℝ} {u : E}
    (hu : (s, u) ∈ Ω) :
    HasFDerivAt (fun v : E ↦ f (s, v)) (spatialFDeriv f (s, u)) u := by
  have hpair : HasFDerivAt (fun v : E ↦ (s, v)) (ContinuousLinearMap.inr ℝ ℝ E) u := by
    convert (hasFDerivAt_const s u).prodMk (hasFDerivAt_id u) using 1 <;> ext v <;> simp
  exact (((hf (s, u) hu).contDiffAt (hΩ.mem_nhds hu)).differentiableAt (by simp)).hasFDerivAt.comp
    u hpair

end Derivative

theorem backwardSquareTime_mem_interior {J : Set ℝ} {T τmax τ₁ τ₂ s : ℝ}
    (hwindow : Icc (T - τmax) T ⊆ J) (hτ₁ : 0 ≤ τ₁)
    (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax)
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) : T - s ^ 2 ∈ interior J := by
  apply interior_mono hwindow
  rw [interior_Icc]
  have hpos : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
  have hsupper : s ^ 2 < τ₂ := by
    simpa only [Real.sq_sqrt (hτ₁.trans hordered.le)] using
      (sq_lt_sq₀ hpos.le (Real.sqrt_nonneg τ₂)).mpr hs.2
  constructor <;> nlinarith [sq_pos_of_pos hpos]

universe uM

variable {n : ℕ} {M : Type uM} [TopologicalSpace M]
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

theorem chart_spatial_coefficient_bounds {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{uM}) (T : ℝ) (x : M) {a b : ℝ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) x).target)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ interior J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc a b, ∀ v ∈ K,
      ‖chartActionMetric F T x (s, v)‖ ≤ C ∧
      ‖spatialFDeriv (chartActionMetric F T x) (s, v)‖ ≤ C ∧
      ‖spatialFDeriv (chartActionPotential F T x) (s, v)‖ ≤ C := by
  have hsub : Icc a b ×ˢ K ⊆ chartActionDomain F T x :=
    fun z hz ↦ ⟨htime z.1 hz.1, hKt hz.2⟩
  have hG := chartActionMetric_contDiffOn F T x
  have hV := chartActionPotential_contDiffOn F hM04 T x
  have hDG := spatialFDeriv_continuousOn (chartActionDomain_open F T x) _ hG
  have hDV := spatialFDeriv_continuousOn (chartActionDomain_open F T x) _ hV
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (f := chartActionMetric F T x)
    (hG.continuousOn.mono hsub)
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hDG.mono hsub)
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hDV.mono hsub)
  refine ⟨|C₀| + |C₁| + |C₂|, by positivity, ?_⟩
  intro s hs v hv
  have h₀ := hC₀ (s, v) ⟨hs, hv⟩
  have h₁ := hC₁ (s, v) ⟨hs, hv⟩
  have h₂ := hC₂ (s, v) ⟨hs, hv⟩
  refine ⟨?_, ?_, ?_⟩ <;>
    linarith [le_abs_self C₀, le_abs_self C₁, le_abs_self C₂,
      abs_nonneg C₀, abs_nonneg C₁, abs_nonneg C₂]

theorem chart_contMDiffAt_of_contDiffOn {a b s : ℝ} (hs : s ∈ Ioo a b)
    (x : M) (γ : ℝ → M)
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hreg : ContDiffOn ℝ 1 ((extChartAt (𝓡 n) x) ∘ γ) (Icc a b)) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ s := by
  let e := extChartAt (𝓡 n) x
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have htarget : MapsTo (e ∘ γ) (Icc a b) e.target :=
    fun r hr ↦ e.map_source (hsrc' hr)
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).of_le
    (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hcomp := hinv.comp hreg.contMDiffOn htarget
  have hγreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b) := by
    apply hcomp.congr
    intro r hr
    exact (e.left_inv (hsrc' hr)).symm
  exact (hγreg s (Ioo_subset_Icc_self hs)).contMDiffAt (Icc_mem_nhds hs.1 hs.2)

section Action

variable {X : Type uM} [MetricSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]

set_option maxHeartbeats 800000 in

theorem chartH1Action_eq_coordinate_integral {J : Set ℝ} (F : RicciFlow n X J)
    (hM04 : RicciFlowCurvatureTheory.{uM}) (T : ℝ) {a b : ℝ} (hab : a ≤ b)
    (x : X) (ξ : ℝ → X) (hξ : ContinuousOn ξ (Icc a b))
    (hsrc : MapsTo ξ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (u : ℝ → EuclideanSpace ℝ (Fin n))
    (hcurve : ∀ s ∈ Icc a b, ξ s = (extChartAt (𝓡 n) x).symm (u s))
    (v : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (d : ℝ → EuclideanSpace ℝ (Fin n))
    (hd : (v : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc a b)] d) :
    chartH1Action F T x a b ξ v =
      ∫ s in a..b, chartActionMetric F T x (s, u s) (d s) (d s) / 2 +
        chartActionPotential F T x (s, u s) := by
  let B := fun s ↦ regularizedChartMetric F T x (s, ξ s)
  have hB : ContinuousOn B (Icc a b) :=
    (regularizedChartMetric_continuousOn F T x
      (K := (chartAt (EuclideanSpace ℝ (Fin n)) x).source) htime Subset.rfl).comp
      (continuousOn_id.prodMk hξ) (fun s hs ↦ ⟨hs, hsrc hs⟩)
  have hkin : IntervalIntegrable (fun s ↦ B s (v s) (v s)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (chart_density_integrable B (continuousOn_memLp_top_Icc hB) v)
  have hV : ContinuousOn (fun s ↦
      2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (ξ s)) (Icc a b) :=
    (regularizedPotential_continuousOn F hM04 T (K := univ) htime).comp
      (continuousOn_id.prodMk hξ) (fun s hs ↦ ⟨hs, mem_univ _⟩)
  rw [chartH1Action, ← intervalIntegral.integral_add hkin (hV.intervalIntegrable_of_Icc hab)]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with s hsd hs
  rw [hsd]
  simp only [B, regularizedChartMetric, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hcurve s hs, chartActionMetric, chartActionPotential]
  ring

end Action

end PoincareConjecture.M08
