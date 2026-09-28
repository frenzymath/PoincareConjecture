import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHalfDiskGreen
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarL2
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerSlicing
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEndpoint
import PoincareConjecture.Proofs.M03.Existence.EuclideanCutoffNative
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap InnerProductSpace LineDeriv

namespace PoincareConjecture.M65Boundary

open M65Interior EuclideanDerivativeNative

private theorem continuous_memLp_compact {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : Continuous f) :
    MemLp f 2 (μ.restrict K) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact hK)

private theorem L2_set_pairing_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A : ℕ → Lp ℝ 2 μ} {U : Lp ℝ 2 μ} (hA : Tendsto A atTop (𝓝 U))
    {w : X → ℝ} (hw : MemLp w 2 μ) (S : Set X) :
    Tendsto (fun n => ∫ z in S, A n z * w z ∂μ) atTop
      (𝓝 (∫ z in S, U z * w z ∂μ)) := by
  let T := LpToLpRestrictCLM X ℝ ℝ μ 2 S
  let W := (hw.restrict S).toLp w
  have heq (v : Lp ℝ 2 μ) :
      ⟪T v, W⟫_ℝ = ∫ z in S, v z * w z ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ S v, (hw.restrict S).coeFn_toLp]
      with z hz hwz
    change ⟪(LpToLpRestrictCLM X ℝ ℝ μ 2 S v) z,
      (hw.restrict S).toLp w z⟫_ℝ = v z * w z
    rw [hz, hwz, Real.inner_apply, mul_comm]
  simpa only [Function.comp_def, heq] using (((T.continuous.tendsto U).comp hA).inner
    (𝕜 := ℝ) (tendsto_const_nhds (x := W)))

private theorem smooth_green_signed_diameter (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z +
        f z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        f (r • Proofs.M58.angularPoint θ) * test (r • Proofs.M58.angularPoint θ) *
          Proofs.M58.angularPoint θ i) -
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
        ∫ s in (-r)..r,
          f (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) *
            test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let h := fun s : ℝ => f (s • b 0) * test (s • b 0)
  have hc : Continuous h :=
    (hf.continuous.comp (continuous_id.smul continuous_const)).mul
      (test.continuous.comp (continuous_id.smul continuous_const))
  have hpi : Proofs.M58.angularPoint Real.pi = -(b 0) := by
    ext j
    fin_cases j <;> simp [b, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  have hzero : Proofs.M58.angularPoint 0 = b 0 := by
    ext j
    fin_cases j <;> simp [b, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  have htpi : Proofs.M58.angularVector Real.pi = -(b 1) := by
    ext j
    fin_cases j <;> simp [b, Proofs.M58.angularVector, EuclideanSpace.basisFun_apply]
  have htzero : Proofs.M58.angularVector 0 = b 1 := by
    ext j
    fin_cases j <;> simp [b, Proofs.M58.angularVector, EuclideanSpace.basisFun_apply]
  have hedge : (∫ s in (0 : ℝ)..r,
      (f (s • Proofs.M58.angularPoint Real.pi) * test (s • Proofs.M58.angularPoint Real.pi) *
        Proofs.M58.angularVector Real.pi i) -
      (f (s • Proofs.M58.angularPoint 0) * test (s • Proofs.M58.angularPoint 0) *
        Proofs.M58.angularVector 0 i)) = -(b 1 i * ∫ s in (-r)..r, h s) := by
    simp only [hpi, hzero, htpi, htzero, PiLp.neg_apply, smul_neg, ← neg_smul]
    have heq (s : ℝ) :
        f ((-s) • b 0) * test ((-s) • b 0) * (-b 1 i) -
          f (s • b 0) * test (s • b 0) * b 1 i =
            -(b 1 i * (h (-s) + h s)) := by dsimp only [h]; ring
    simp_rw [heq]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    have hneg : IntervalIntegrable (fun x => h (-x)) volume 0 r :=
      (hc.comp continuous_neg).intervalIntegrable 0 r
    rw [intervalIntegral.integral_add hneg (hc.intervalIntegrable 0 r),
      intervalIntegral.integral_comp_neg, neg_zero,
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-r) 0)
        (hc.intervalIntegrable 0 r)]
  have heq := smooth_halfDisk_green f test hf (test.smooth 1) i hr
  rw [hedge] at heq
  exact heq

private theorem halfDisk_polar_mem {ε R H : ℝ} (hε : 0 < ε) (hRH : R ≤ H)
    {r θ : ℝ} (hr : r ∈ Icc ε R) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    polarPlane 0 (r, θ) ∈ closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1} := by
  have hr0 : 0 ≤ r := hε.le.trans hr.1
  constructor
  · rw [mem_closedBall_zero_iff]
    simpa only [polarPlane, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0,
      Proofs.M58.norm_angularPoint, mul_one] using hr.2.trans hRH
  · change 0 ≤ (0 + r • Proofs.M58.angularPoint θ) 1
    simp only [zero_add, PiLp.smul_apply, smul_eq_mul, Proofs.M58.angularPoint,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact mul_nonneg hr0 (Real.sin_nonneg_of_mem_Icc hθ)

private theorem halfDisk_polar_map_le {ε R H : ℝ} (hε : 0 < ε) (hRH : R ≤ H) :
    Measure.map (polarPlane 0)
      ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))) ≤
        (ENNReal.ofReal ε)⁻¹ •
          volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}) := by
  let μ := (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  have hm := (polarPlane_measurePreserving (0 : LoopPlane)).measurable
  have hangle : Icc (0 : ℝ) Real.pi ⊆ Icc (-Real.pi) Real.pi :=
    Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hbound : Measure.map (polarPlane 0) μ ≤
      (ENNReal.ofReal ε)⁻¹ • (volume : Measure LoopPlane) :=
    (Measure.map_mono (Measure.prod_mono le_rfl
      (Measure.restrict_mono hangle le_rfl)) hm).trans (polarPlane_map_strip_le 0 hε)
  have hmem : ∀ᵐ z ∂Measure.map (polarPlane 0) μ, z ∈ K := by
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    change ∀ᵐ p ∂μ, polarPlane 0 p ∈ K
    dsimp only [μ]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact halfDisk_polar_mem hε hRH hp.1 hp.2
  calc
    Measure.map (polarPlane 0) μ = (Measure.map (polarPlane 0) μ).restrict K :=
      (Measure.restrict_eq_self_of_ae_mem hmem).symm
    _ ≤ ((ENNReal.ofReal ε)⁻¹ • (volume : Measure LoopPlane)).restrict K :=
      Measure.restrict_mono Subset.rfl hbound
    _ = _ := Measure.restrict_smul _ _ _





theorem halfDisk_graph_green {ε R H : ℝ} (hε : 0 < ε) (hRH : R ≤ H)
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (A : ℕ → Lp ℝ 2 (volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (D : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (U : Lp ℝ 2 (volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (d : Fin 2 → Lp ℝ 2 (volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (B : ℕ → Lp ℝ 2 (volume.restrict (Icc (-H) H)))
    (b : Lp ℝ 2 (volume.restrict (Icc (-H) H)))
    (hA : ∀ n, A n =ᵐ[volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})] f n)
    (hD : ∀ n i, D n i =ᵐ[volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})]
        fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hB : ∀ n, B n =ᵐ[volume.restrict (Icc (-H) H)]
      fun s => f n (s • EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (hAU : Tendsto A atTop (𝓝 U))
    (hDd : ∀ i, Tendsto (fun n => D n i) atTop (𝓝 (d i)))
    (hBb : Tendsto B atTop (𝓝 b)) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      MemLp (fun θ => U (r • Proofs.M58.angularPoint θ))
        2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
        (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
          d i z * test z + U z *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          r * (∫ θ in (0 : ℝ)..Real.pi,
            U (r • Proofs.M58.angularPoint θ) * test (r • Proofs.M58.angularPoint θ) *
              Proofs.M58.angularPoint θ i) -
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
              ∫ s in (-r)..r, b s * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  let μ : Measure LoopPlane := volume.restrict K
  let ρ : Measure ℝ := volume.restrict (Icc ε R)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) Real.pi)
  let C := (ENNReal.ofReal ε)⁻¹
  have hC : C ≠ (⊤ : ENNReal) :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hdom : Measure.map (polarPlane 0) (ρ.prod ν) ≤ C • μ :=
    halfDisk_polar_map_le hε hRH
  have hm := (polarPlane_measurePreserving (0 : LoopPlane)).measurable
  let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ρ.prod ν) :=
    ChartLpNative.dominatedPullbackL2 (polarPlane 0) hm.aemeasurable hC hdom
  have hT (V : Lp ℝ 2 μ) : T V =ᵐ[ρ.prod ν] fun p => V (p.1 • Proofs.M58.angularPoint p.2) := by
    simpa only [Function.comp_def, polarPlane, zero_add] using
      ChartLpNative.dominatedPullbackL2_coe (polarPlane 0) hm.aemeasurable hC hdom V
  have hTf (n : ℕ) : T (A n) =ᵐ[ρ.prod ν]
      fun p => f n (p.1 • Proofs.M58.angularPoint p.2) := by
    have ha := ae_of_ae_map hm.aemeasurable
      (ae_mono hdom (Measure.ae_smul_measure (hA n) C))
    apply (hT (A n)).trans
    filter_upwards [ha] with p hp
    simpa only [polarPlane, zero_add] using hp
  obtain ⟨σ, hσ, hslice⟩ :=
    m65L2_exists_slice_subsequence ((T.continuous.tendsto U).comp hAU)
  have hfn : ∀ᵐ r ∂ρ, ∀ n, ∀ᵐ θ ∂ν,
      T (A n) (r, θ) = f n (r • Proofs.M58.angularPoint θ) :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hTf n))
  have hu := Measure.ae_ae_of_ae_prod (hT U)
  filter_upwards [hslice, hfn, hu, ae_restrict_mem measurableSet_Icc]
    with r hrSlice hfr hur hr
  obtain ⟨hVn, hV0, hVconv⟩ := hrSlice
  let Vn (n : ℕ) := (hVn n).toLp (fun θ => T (A (σ n)) (r, θ))
  let V0 := hV0.toLp (fun θ => T U (r, θ))
  have hVnf (n : ℕ) : Vn n =ᵐ[ν] fun θ => f (σ n) (r • Proofs.M58.angularPoint θ) :=
    (hVn n).coeFn_toLp.trans (hfr (σ n))
  have hV0u : V0 =ᵐ[ν] fun θ => U (r • Proofs.M58.angularPoint θ) :=
    hV0.coeFn_toLp.trans hur
  refine ⟨(Lp.memLp V0).ae_eq hV0u, ?_⟩
  intro test i
  have hr0 : 0 < r := hε.trans_le hr.1
  have hrH : r ≤ H := hr.2.trans hRH
  let Kr := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  have hKrK : Kr ⊆ K := inter_subset_inter
    (closedBall_subset_closedBall hrH) Subset.rfl
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) H).inter_right
    (isClosed_le continuous_const (by fun_prop))
  have htest : MemLp test 2 μ := continuous_memLp_compact hK test.continuous
  have hpartial : Continuous (fun z =>
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
    ((test.smooth 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have htestD : MemLp (fun z =>
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 μ :=
    continuous_memLp_compact hK hpartial
  have hleft := (L2_set_pairing_tendsto ((hDd i).comp hσ.tendsto_atTop) htest Kr).add
    (L2_set_pairing_tendsto (hAU.comp hσ.tendsto_atTop) htestD Kr)
  have hleft_eq (V W : Lp ℝ 2 μ) :
      (∫ z in Kr, V z * test z ∂μ) +
        (∫ z in Kr, W z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) ∂μ) =
      ∫ z in Kr, V z * test z +
        W z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    have hVI : Integrable (fun z => V z * test z) (μ.restrict Kr) :=
      ((Lp.memLp V).integrable_mul htest).integrableOn
    have hWI : Integrable (fun z => W z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) (μ.restrict Kr) :=
      ((Lp.memLp W).integrable_mul htestD).integrableOn
    rw [← integral_add hVI hWI]
    exact congrArg (fun m : Measure LoopPlane => ∫ z,
      V z * test z + W z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) ∂m)
      (Measure.restrict_restrict_of_subset hKrK)
  change Tendsto (fun n => (∫ z in Kr, D (σ n) i z * test z ∂μ) +
      ∫ z in Kr, A (σ n) z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) ∂μ) atTop
    (𝓝 ((∫ z in Kr, d i z * test z ∂μ) + ∫ z in Kr, U z *
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) ∂μ)) at hleft
  simp_rw [hleft_eq] at hleft
  let w := fun θ => test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i
  have hw : MemLp w 2 ν := continuous_memLp_compact isCompact_Icc (by
    dsimp only [w]
    have hang := Proofs.M58.contDiff_angularPoint.continuous
    fun_prop)
  have hright0 := L2_set_pairing_tendsto hVconv hw univ
  simp only [setIntegral_univ] at hright0
  have hsem (V : Lp ℝ 2 ν) (q : ℝ → ℝ) (hVq : V =ᵐ[ν] q) :
      (∫ θ, V θ * w θ ∂ν) = ∫ θ in (0 : ℝ)..Real.pi,
        q θ * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [hVq] with θ hθ
    dsimp only [w]
    rw [hθ, mul_assoc]
  have hsemconv := hright0.congr (fun n => hsem (Vn n) _ (hVnf n))
  rw [hsem V0 _ hV0u] at hsemconv
  let wB := fun s : ℝ => test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hwB : MemLp wB 2 (volume.restrict (Icc (-H) H)) :=
    continuous_memLp_compact isCompact_Icc
      (test.continuous.comp (continuous_id.smul continuous_const))
  have hdiam := L2_set_pairing_tendsto (hBb.comp hσ.tendsto_atTop) hwB (Icc (-r) r)
  have hdiam_eq (V : Lp ℝ 2 (volume.restrict (Icc (-H) H))) :
      (∫ s in Icc (-r) r, V s * wB s ∂volume.restrict (Icc (-H) H)) =
        ∫ s in (-r)..r, V s * wB s := by
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc (neg_le_neg hrH) hrH),
      intervalIntegral.integral_of_le (by linarith : -r ≤ r),
      ← integral_Icc_eq_integral_Ioc]
  simp only [hdiam_eq] at hdiam
  have hright := (hsemconv.const_mul r).sub
    (hdiam.const_mul ((EuclideanSpace.basisFun (Fin 2) ℝ 1) i))
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro n
  have hAn : A (σ n) =ᵐ[volume.restrict Kr] f (σ n) :=
    ae_restrict_of_ae_restrict_of_subset hKrK (hA (σ n))
  have hDn := ae_restrict_of_ae_restrict_of_subset hKrK (hD (σ n) i)
  have hBn := ae_restrict_of_ae_restrict_of_subset
    ((uIoc_subset_uIcc).trans (by
      rw [uIcc_of_le (by linarith : -r ≤ r)]
      exact Icc_subset_Icc (neg_le_neg hrH) hrH)) (hB (σ n))
  have hlefteq : (∫ z in Kr, D (σ n) i z * test z +
      A (σ n) z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      ∫ z in Kr, fderiv ℝ (f (σ n)) z (EuclideanSpace.basisFun (Fin 2) ℝ i) * test z +
        f (σ n) z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    apply integral_congr_ae
    filter_upwards [hAn, hDn] with z haz hdz
    rw [haz, hdz]
  have hdiamActual : (∫ s in (-r)..r, B (σ n) s * wB s) =
      ∫ s in (-r)..r, f (σ n) (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) * wB s := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hBn] with s hs
    rw [hs]
  dsimp only [Function.comp_def]
  rw [hdiamActual]
  exact (hlefteq.trans (smooth_green_signed_diameter _ (hf (σ n)) test i hr0)).symm

private theorem halfStrip_angular_operator {ε R H : ℝ} (hε : 0 < ε) (hRH : R ≤ H) :
    let μ := volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})
    let ν := (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))
    ∃ T : (Fin 2 → Lp ℝ 2 μ) →L[ℝ] Lp ℝ 2 ν,
      ∀ d, T d =ᵐ[ν] fun p =>
        -p.1 * Real.sin p.2 * d 0 (p.1 • Proofs.M58.angularPoint p.2) +
          p.1 * Real.cos p.2 * d 1 (p.1 • Proofs.M58.angularPoint p.2) := by
  let μ := volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})
  let ν := (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))
  have hC : (ENNReal.ofReal ε)⁻¹ ≠ (⊤ : ENNReal) :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hm := (polarPlane_measurePreserving (0 : LoopPlane)).measurable
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
    ChartLpNative.dominatedPullbackL2 (polarPlane 0) hm.aemeasurable hC
      (halfDisk_polar_map_le hε hRH)
  have hL (v : Lp ℝ 2 μ) : L v =ᵐ[ν]
      fun p => v (p.1 • Proofs.M58.angularPoint p.2) := by
    simpa only [Function.comp_def, polarPlane, zero_add] using
      ChartLpNative.dominatedPullbackL2_coe (polarPlane 0) hm.aemeasurable hC
        (halfDisk_polar_map_le hε hRH) v
  let c (i : Fin 2) (p : ℝ × ℝ) := if i = 0 then -p.1 * Real.sin p.2
    else p.1 * Real.cos p.2
  have hc (i : Fin 2) : Continuous (c i) := by
    dsimp only [c]
    split_ifs <;> fun_prop
  have hb (i : Fin 2) : ∀ᵐ p ∂ν, ‖c i p‖ ≤ R := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hp0 : 0 ≤ p.1 := hε.le.trans hp.1.1
    dsimp only [c]
    split_ifs
    · simp only [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hp0]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one p.2) hp0).trans
        (by simpa only [mul_one] using hp.1.2)
    · simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp0]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2) hp0).trans
        (by simpa only [mul_one] using hp.1.2)
  let A (i : Fin 2) (p : ℝ × ℝ) := c i p • ContinuousLinearMap.id ℝ ℝ
  have hA (i : Fin 2) : AEStronglyMeasurable (A i) ν :=
    ((hc i).smul continuous_const).aestronglyMeasurable
  have hAb (i : Fin 2) : ∀ᵐ p ∂ν, ‖A i p‖ ≤ R := by
    filter_upwards [hb i] with p hp
    simpa only [A, norm_smul, ContinuousLinearMap.norm_id, mul_one] using hp
  let B (i : Fin 2) := Lp.coefficientL2 (A i) (hA i) R (hAb i)
  let T : (Fin 2 → Lp ℝ 2 μ) →L[ℝ] Lp ℝ 2 ν :=
    ((B 0).comp L).comp (ContinuousLinearMap.proj 0) +
      ((B 1).comp L).comp (ContinuousLinearMap.proj 1)
  refine ⟨T, ?_⟩
  intro d
  filter_upwards [Lp.coeFn_add (B 0 (L (d 0))) (B 1 (L (d 1))),
    Lp.coefficientL2_ae (A 0) (hA 0) R (hAb 0) (L (d 0)),
    Lp.coefficientL2_ae (A 1) (hA 1) R (hAb 1) (L (d 1)),
    hL (d 0), hL (d 1)] with p hp h0 h1 hl0 hl1
  change (B 0 (L (d 0)) + B 1 (L (d 1)) : Lp ℝ 2 ν) p = _
  rw [hp]
  change B 0 (L (d 0)) p + B 1 (L (d 1)) p = _
  rw [h0, h1]
  simp [A, c, hl0, hl1]

private theorem smooth_semicircle_derivative (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (r θ : ℝ) :
    deriv (fun t => f (r • Proofs.M58.angularPoint t)) θ =
      -r * Real.sin θ * fderiv ℝ f (r • Proofs.M58.angularPoint θ)
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        r * Real.cos θ * fderiv ℝ f (r • Proofs.M58.angularPoint θ)
          (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
  have hv : r • Proofs.M58.angularVector θ =
      (-r * Real.sin θ) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        (r * Real.cos θ) • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularVector, EuclideanSpace.basisFun_apply]
  have hd := ((hf.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt θ
    ((Proofs.M58.hasDerivAt_angularPoint θ).const_smul r)
  change HasDerivAt (fun t => f (r • Proofs.M58.angularPoint t))
    (fderiv ℝ f (r • Proofs.M58.angularPoint θ) (r • Proofs.M58.angularVector θ)) θ at hd
  rw [hd.deriv, hv, map_add, map_smul, map_smul]
  rfl






theorem halfDisk_graph_AC {ε R H : ℝ} (hε : 0 < ε) (hRH : R ≤ H)
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (A : ℕ → Lp ℝ 2 (volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (D : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (U : Lp ℝ 2 (volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (d : Fin 2 → Lp ℝ 2 (volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})))
    (B : ℕ → Lp ℝ 2 (volume.restrict (Icc (-H) H)))
    (b : Lp ℝ 2 (volume.restrict (Icc (-H) H)))
    (hA : ∀ n, A n =ᵐ[volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})] f n)
    (hD : ∀ n i, D n i =ᵐ[volume.restrict
      (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})]
        fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hB : ∀ n, B n =ᵐ[volume.restrict (Icc (-H) H)]
      fun s => f n (s • EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (hAU : Tendsto A atTop (𝓝 U))
    (hDd : ∀ i, Tendsto (fun n => D n i) atTop (𝓝 (d i)))
    (hBb : Tendsto B atTop (𝓝 b)) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      MemLp (fun θ => -r * Real.sin θ * d 0 (r • Proofs.M58.angularPoint θ) +
        r * Real.cos θ * d 1 (r • Proofs.M58.angularPoint θ))
          2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
          fun θ => U (r • Proofs.M58.angularPoint θ)) ∧
        v 0 = b r ∧ v Real.pi = b (-r) ∧
        ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ θ in s..t,
            -r * Real.sin θ * d 0 (r • Proofs.M58.angularPoint θ) +
              r * Real.cos θ * d 1 (r • Proofs.M58.angularPoint θ) := by
  let μ := volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})
  let ρ : Measure ℝ := volume.restrict (Icc ε R)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) Real.pi)
  let μB : Measure ℝ := volume.restrict (Icc (-H) H)
  have hC : (ENNReal.ofReal ε)⁻¹ ≠ (⊤ : ENNReal) :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hm := (polarPlane_measurePreserving (0 : LoopPlane)).measurable
  have hdom := halfDisk_polar_map_le hε hRH
  let T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ρ.prod ν) :=
    ChartLpNative.dominatedPullbackL2 (polarPlane 0) hm.aemeasurable hC hdom
  have hT (V : Lp ℝ 2 μ) : T V =ᵐ[ρ.prod ν]
      fun p => V (p.1 • Proofs.M58.angularPoint p.2) := by
    simpa only [Function.comp_def, polarPlane, zero_add] using
      ChartLpNative.dominatedPullbackL2_coe (polarPlane 0) hm.aemeasurable hC hdom V
  have hcomp {u v : LoopPlane → ℝ} (h : u =ᵐ[μ] v) :
      (fun p : ℝ × ℝ => u (p.1 • Proofs.M58.angularPoint p.2)) =ᵐ[ρ.prod ν]
        fun p => v (p.1 • Proofs.M58.angularPoint p.2) := by
    have hh := ae_of_ae_map hm.aemeasurable
      (ae_mono hdom (Measure.ae_smul_measure h (ENNReal.ofReal ε)⁻¹))
    filter_upwards [hh] with p hp
    simpa only [polarPlane, zero_add] using hp
  obtain ⟨E, hE⟩ := halfStrip_angular_operator hε hRH
  let F (n : ℕ) (r θ : ℝ) := f n (r • Proofs.M58.angularPoint θ)
  have hFs (n : ℕ) (r : ℝ) : ContDiff ℝ 1 (F n r) :=
    (hf n).comp ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).const_smul r)
  have hTf (n : ℕ) : T (A n) =ᵐ[ρ.prod ν] fun p => F n p.1 p.2 :=
    (hT (A n)).trans (hcomp (hA n))
  have hEf (n : ℕ) : E (D n) =ᵐ[ρ.prod ν] fun p => deriv (F n p.1) p.2 := by
    filter_upwards [hE (D n), hcomp (hD n 0), hcomp (hD n 1)] with p hp h0 h1
    rw [hp, h0, h1]
    exact (smooth_semicircle_derivative (f n) (hf n) p.1 p.2).symm
  obtain ⟨σ, hσ, hBpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hBb).exists_seq_tendsto_ae
  have hBactual : ∀ᵐ s ∂μB,
      Tendsto (fun n => f (σ n) (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) atTop
        (𝓝 (b s)) := by
    filter_upwards [hBpoint, ae_all_iff.mpr hB] with s hs hBs
    exact hs.congr (fun n => hBs (σ n))
  have hnegPre : (fun s : ℝ => -s) ⁻¹' Icc (-H) H = Icc (-H) H := by
    ext s
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  have hnegμ := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (Icc (-H) H)
  rw [hnegPre] at hnegμ
  have hRsub : Icc ε R ⊆ Icc (-H) H := by
    intro r hr
    have hp : 0 < r := hε.trans_le hr.1
    have hrH : r ≤ H := hr.2.trans hRH
    exact ⟨by linarith, hrH⟩
  have hBpos := ae_restrict_of_ae_restrict_of_subset hRsub hBactual
  have hBneg := ae_restrict_of_ae_restrict_of_subset hRsub
    (hnegμ.quasiMeasurePreserving.ae hBactual)
  obtain ⟨τ, hτ, hUslice⟩ := m65L2_exists_slice_subsequence
    (((T.continuous.tendsto U).comp hAU).comp hσ.tendsto_atTop)
  have hDlim := (E.continuous.tendsto d).comp (tendsto_pi_nhds.mpr hDd)
  obtain ⟨kappa, hkappa, hDslice⟩ := m65L2_exists_slice_subsequence
    ((hDlim.comp hσ.tendsto_atTop).comp hτ.tendsto_atTop)
  have hUf : ∀ᵐ r ∂ρ, ∀ n, ∀ᵐ θ ∂ν, T (A n) (r, θ) = F n r θ :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hTf n))
  have hDf : ∀ᵐ r ∂ρ, ∀ n, ∀ᵐ θ ∂ν, E (D n) (r, θ) = deriv (F n r) θ :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hEf n))
  filter_upwards [hUslice, hDslice, hUf, hDf, Measure.ae_ae_of_ae_prod (hT U),
    Measure.ae_ae_of_ae_prod (hE d), hBpos, hBneg]
    with r hUr hDr hUfr hDfr hur hdr hbr hbneg
  obtain ⟨hUn, hU0, hUconv⟩ := hUr
  obtain ⟨hDn, hD0, hDconv⟩ := hDr
  let Un (n : ℕ) := (hUn (kappa n)).toLp (fun θ => T (A (σ (τ (kappa n)))) (r, θ))
  let Dn (n : ℕ) := (hDn n).toLp (fun θ => E (D (σ (τ (kappa n)))) (r, θ))
  let U0 := hU0.toLp (fun θ => T U (r, θ))
  let D0 := hD0.toLp (fun θ => E d (r, θ))
  have hUnf (n : ℕ) : Un n =ᵐ[ν] F (σ (τ (kappa n))) r :=
    (hUn (kappa n)).coeFn_toLp.trans (hUfr (σ (τ (kappa n))))
  have hDnf (n : ℕ) : Dn n =ᵐ[ν] deriv (F (σ (τ (kappa n))) r) :=
    (hDn n).coeFn_toLp.trans (hDfr (σ (τ (kappa n))))
  have hD0d : D0 =ᵐ[ν] fun θ =>
      -r * Real.sin θ * d 0 (r • Proofs.M58.angularPoint θ) +
        r * Real.cos θ * d 1 (r • Proofs.M58.angularPoint θ) :=
    hD0.coeFn_toLp.trans hdr
  obtain ⟨v, hvAC, hvAE, hvint, hvpoint⟩ := m65Interval_AC_graph_endpoint_limit Real.pi_pos
    (fun n => F (σ (τ (kappa n))) r) (fun n => hFs (σ (τ (kappa n))) r)
    Un Dn U0 D0 hUnf hDnf (hUconv.comp hkappa.tendsto_atTop) hDconv
  have hzero : Proofs.M58.angularPoint 0 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  have hpi : Proofs.M58.angularPoint Real.pi = -EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  refine ⟨(Lp.memLp D0).ae_eq hD0d, v, hvAC,
    hvAE.trans (hU0.coeFn_toLp.trans hur), ?_, ?_, ?_⟩
  · have hh := hvpoint 0 ⟨le_rfl, Real.pi_pos.le⟩
    simp only [F, hzero] at hh
    exact tendsto_nhds_unique hh ((hbr.comp hτ.tendsto_atTop).comp hkappa.tendsto_atTop)
  · have hh := hvpoint Real.pi ⟨Real.pi_pos.le, le_rfl⟩
    simp only [F, hpi, smul_neg, ← neg_smul] at hh
    exact tendsto_nhds_unique hh ((hbneg.comp hτ.tendsto_atTop).comp hkappa.tendsto_atTop)
  · intro s hs t ht
    rw [hvint s hs t ht]
    apply intervalIntegral.integral_congr_ae_restrict
    exact ae_restrict_of_ae_restrict_of_subset
      ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hs ht)) hD0d

end PoincareConjecture.M65Boundary
