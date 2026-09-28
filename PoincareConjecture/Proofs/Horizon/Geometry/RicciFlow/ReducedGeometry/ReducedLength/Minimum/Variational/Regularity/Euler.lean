import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Minimizer
import Mathlib.Analysis.ODE.PicardLindelof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variational

section SmoothCoefficients

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem spatialFDeriv_contDiffOn {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (spatialFDeriv f) Ω := by
  exact (hf.fderiv_of_isOpen hΩ (by simp)).clm_comp contDiffOn_const

end SmoothCoefficients

section Force

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem chartForceVector_contDiff :
    ContDiff ℝ ∞ (fun z : ((E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) × E ↦
      chartForceVector z.1.1 z.1.2 z.2) := by
  have hD : ContDiff ℝ ∞
      (fun z : ((E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) × E ↦ z.1.1) :=
    contDiff_fst.fst
  have hDf := (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.contDiff.comp hD
  have hDq := hDf.clm_apply contDiff_snd
  have hDqf := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.contDiff.comp hDq
  have hDqq := hDqf.clm_apply contDiff_snd
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (((contDiff_const (c := (1 / 2 : ℝ))).smul hDqq).add contDiff_fst.snd)

theorem chartForceVector_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    {DG : X → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {DV : X → E →L[ℝ] ℝ} {q : X → E}
    (hDG : ContinuousOn DG S) (hDV : ContinuousOn DV S) (hq : ContinuousOn q S) :
    ContinuousOn (fun s ↦ chartForceVector (DG s) (DV s) (q s)) S := by
  have hDf := (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.comp_continuousOn hDG
  have hDq := hDf.clm_apply hq
  have hDqf := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous.comp_continuousOn hDq
  have hDqq := hDqf.clm_apply hq
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (((continuousOn_const (c := (1 / 2 : ℝ))).smul hDqq).add hDV)

end Force

universe uM

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

noncomputable def chartEulerPhase {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    (s : ℝ) (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let v := Ring.inverse (chartMetricOperator F T x (s, z.1)) z.2
  (v, chartForceVector (spatialFDeriv (chartActionMetric F T x) (s, z.1))
    (spatialFDeriv (chartActionPotential F T x) (s, z.1)) v)

set_option maxHeartbeats 800000 in

theorem chartEulerPhase_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ)
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)) (x : M) {a b : ℝ}
    (htime : ∀ s ∈ Icc a b, s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    ContDiffOn ℝ ∞ (Function.uncurry (chartEulerPhase F T x))
      (Icc a b ×ˢ ((extChartAt (𝓡 n) x).target ×ˢ univ)) := by
  let Ω := Icc a b ×ˢ ((extChartAt (𝓡 n) x).target ×ˢ
    (univ : Set (EuclideanSpace ℝ (Fin n))))
  let k := fun z : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦ (z.1, z.2.1)
  have hk : ContDiffOn ℝ ∞ k Ω := contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmap : MapsTo k Ω (chartActionDomain F T x) :=
    fun z hz ↦ ⟨htime z.1 hz.1, hz.2.1⟩
  have hB := (chartMetricInverse_contDiffOn F T x).comp hk hmap
  have hv := hB.clm_apply contDiffOn_snd.snd
  have hDG := (spatialFDeriv_contDiffOn (chartActionDomain_open F T x) _
    (chartActionMetric_contDiffOn F T x)).comp hk hmap
  have hDV := (spatialFDeriv_contDiffOn (chartActionDomain_open F T x) _
    (chartActionPotential_contDiffOn F T hpotential x)).comp hk hmap
  have hQ := (chartForceVector_contDiff (E := EuclideanSpace ℝ (Fin n))).comp_contDiffOn
    ((hDG.prodMk hDV).prodMk hv)
  exact hv.prodMk hQ

set_option maxHeartbeats 1200000 in

theorem chart_minimum_smooth_momentum {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ)
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)) {a b : ℝ} (hab : a < b)
    (x : M) (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J))
    (w : IntervalL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hw : ∀ s ∈ Icc a b, extChartAt (𝓡 n) x (γ s) =
      extChartAt (𝓡 n) x (γ a) + ∫ r in a..s, w r)
    (hmin : IsChartH1Minimizer F T x a b γ w) :
    let u : ℝ → EuclideanSpace ℝ (Fin n) := extChartAt (𝓡 n) x ∘ γ
    ContDiffOn ℝ ∞ u (Icc a b) ∧ ∀ s ∈ Ioo a b,
      HasDerivAt (fun r ↦ chartMomentumVector (chartActionMetric F T x (r, u r)) (deriv u r))
        (chartForceVector (spatialFDeriv (chartActionMetric F T x) (s, u s))
          (spatialFDeriv (chartActionPotential F T x) (s, u s)) (deriv u s)) s := by
  let e := extChartAt (𝓡 n) x
  let u : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  let q := derivWithin u (Icc a b)
  have hreg : ContDiffOn ℝ 1 u (Icc a b) :=
    chart_minimum_contDiffOn F T hpotential hab x γ hγ hsrc htime w hw hmin
  have hq : ContinuousOn q (Icc a b) :=
    hreg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by rfl)
  have hud (s : ℝ) (hs : s ∈ Icc a b) : HasDerivWithinAt u (q s) (Icc a b) s :=
    ((hreg.differentiableOn (by simp)) s hs).hasDerivWithinAt
  have hwq : (w : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc a b)] q := by
    filter_upwards [primitive_ae_hasDerivAt hab.le u w hw,
      ae_restrict_mem measurableSet_Icc] with s hs hmem
    exact (hs.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab s hmem)).symm
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have hpair : ContinuousOn (fun s ↦ (s, u s)) (Icc a b) :=
    continuousOn_id.prodMk hreg.continuousOn
  have hdom : MapsTo (fun s ↦ (s, u s)) (Icc a b) (chartActionDomain F T x) :=
    fun s hs ↦ ⟨htime s hs, e.map_source (hsrc' hs)⟩
  let G := fun s ↦ chartActionMetric F T x (s, u s)
  let DG := fun s ↦ spatialFDeriv (chartActionMetric F T x) (s, u s)
  let DV := fun s ↦ spatialFDeriv (chartActionPotential F T x) (s, u s)
  let P := fun s ↦ chartMomentumVector (G s) (q s)
  let Q := fun s ↦ chartForceVector (DG s) (DV s) (q s)
  have hG : ContinuousOn G (Icc a b) :=
    (chartActionMetric_contDiffOn F T x).continuousOn.comp hpair hdom
  have hDG : ContinuousOn DG (Icc a b) :=
    (spatialFDeriv_continuousOn (chartActionDomain_open F T x) _
      (chartActionMetric_contDiffOn F T x)).comp hpair hdom
  have hDV : ContinuousOn DV (Icc a b) :=
    (spatialFDeriv_continuousOn (chartActionDomain_open F T x) _
      (chartActionPotential_contDiffOn F T hpotential x)).comp hpair hdom
  have hP : ContinuousOn P (Icc a b) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp_continuousOn
      (hG.clm_apply hq)
  have hQ : ContinuousOn Q (Icc a b) :=
    chartForceVector_continuousOn hDG hDV hq
  have hPint : IntervalIntegrable P volume a b := hP.intervalIntegrable_of_Icc hab.le
  have hQint : IntervalIntegrable Q volume a b := hQ.intervalIntegrable_of_Icc hab.le
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • P s) =
        -(∫ s in a..b, φ s • Q s) := by
    intro φ hφ _ hsupp
    have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
      (fun ha ↦ (lt_irrefl a) (hsupp ha).1)
    have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
      (fun hb ↦ (lt_irrefl b) (hsupp hb).2)
    apply weak_momentum_of_scalar_stationarity P Q hPint hQint φ hφ
    intro z
    have hstat := chart_minimum_affine_stationary F T hpotential hab x γ hγ hsrc htime w hw hmin
      (fun s ↦ φ s • z) (fun s ↦ deriv φ s • z)
      (hφ.continuous.continuousOn.smul continuousOn_const)
      ((hφ.continuous_deriv (by simp)).continuousOn.smul continuousOn_const)
      (fun s _ ↦ ((hφ.differentiable (by simp)) s).hasDerivAt.smul_const z)
      (by simp only [hφa, zero_smul]) (by simp only [hφb, zero_smul])
    calc
      _ = ∫ s in a..b, DG s (φ s • z) (q s) (q s) / 2 +
          G s (q s) (deriv φ s • z) + DV s (φ s • z) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only [P, Q]
        rw [chartMomentumVector_inner, chartForceVector_inner]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      _ = ∫ s in a..b, DG s (φ s • z) (w s) (w s) / 2 +
          G s (w s) (deriv φ s • z) + DV s (φ s • z) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le hab.le]
        filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hwq] with s hs
        rw [hs]
      _ = 0 := hstat
  obtain ⟨c, hc⟩ := weak_momentum_primitive hab P Q hPint hQint hweak
  have hpc : ∀ s ∈ Icc a b, P s = c + ∫ r in a..s, Q r := by
    apply Measure.eqOn_Icc_of_ae_eq volume hab.ne hc hP
    have h := intervalIntegral.continuousOn_primitive_interval' hQint left_mem_uIcc
    rw [uIcc_of_le hab.le] at h
    exact continuousOn_const.add h
  have hca : c = P a := by
    simpa only [intervalIntegral.integral_same, add_zero] using (hpc a ⟨le_rfl, hab.le⟩).symm
  have hPprimitive (s : ℝ) (hs : s ∈ Icc a b) : P s = P a + ∫ r in a..s, Q r := by
    rw [hpc s hs, hca]
  obtain ⟨hPd, _⟩ := continuous_primitive_regular hab P Q hQ hPprimitive
  have hinv (s : ℝ) (hs : s ∈ Icc a b) :
      Ring.inverse (chartMetricOperator F T x (s, u s)) (P s) = q s :=
    inverse_operator_apply _ (chartMetricOperator_isUnit F T x (hdom hs)) (q s)
  have hphase (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun r ↦ (u r, P r))
        (chartEulerPhase F T x s (u s, P s)) (Icc a b) s := by
    simpa only [chartEulerPhase, hinv s hs] using (hud s hs).prodMk (hPd s hs)
  have hphasemem : MapsTo (fun s ↦ (u s, P s)) (Icc a b)
      ((extChartAt (𝓡 n) x).target ×ˢ univ) :=
    fun s hs ↦ ⟨(hdom hs).2, mem_univ _⟩
  have hphaseSmooth := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
    (chartEulerPhase_contDiffOn F T hpotential x htime) hphase hphasemem
  refine ⟨hphaseSmooth.fst, ?_⟩
  intro s hs
  have hqs : q s = deriv u s := derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  have heq : (fun r ↦ chartMomentumVector (G r) (deriv u r)) =ᶠ[𝓝 s] P := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    dsimp only [P, q]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)]
  have hd := ((hPd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq heq
  simpa only [Q, hqs] using hd

end PoincareConjecture.ReducedLengthMinimum.Variational
