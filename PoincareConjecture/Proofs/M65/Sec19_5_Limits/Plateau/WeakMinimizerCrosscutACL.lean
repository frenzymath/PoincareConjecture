import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryGraph
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCrosscutBoundary
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEndpoint
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarL2
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerSlicing
import PoincareConjecture.Proofs.M03.Existence.EuclideanCutoffNative
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff InnerProductSpace ENNReal intervalIntegral

namespace PoincareConjecture

open M65Interior EuclideanDerivativeNative

private theorem m65Crosscut_deriv (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (x : LoopPlane) (r t : ℝ) :
    deriv (fun s => f (polarPlane x (r, s))) t =
      -r * Real.sin t * fderiv ℝ f (polarPlane x (r, t))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      r * Real.cos t * fderiv ℝ f (polarPlane x (r, t))
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
  have h := (hf.differentiable one_ne_zero (polarPlane x (r, t))).hasFDerivAt.comp_hasDerivAt t
    (((Proofs.M58.hasDerivAt_angularPoint t).const_smul r).const_add x)
  have hv : r • Proofs.M58.angularVector t =
      (-r * Real.sin t) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        (r * Real.cos t) • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularVector, EuclideanSpace.basisFun_apply]
  change HasDerivAt (fun s => f (polarPlane x (r, s))) _ t at h
  rw [h.deriv, hv, map_add, map_smul, map_smul]
  rfl

set_option maxHeartbeats 1600000 in






theorem m65WeakTrace_crosscut_AC
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b))
    {ε R : ℝ} (hε : 0 < ε) (hR : R ≤ 1) :
    ∀ᵐ r ∂volume.restrict (Icc ε R), ∃ v : ℝ → ℝ,
      AbsolutelyContinuousOnInterval v (-m65CrosscutAngle r) (m65CrosscutAngle r) ∧
      (v =ᵐ[volume.restrict (Icc (-m65CrosscutAngle r) (m65CrosscutAngle r))]
        fun t => u (polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0) (r, t))) ∧
      MemLp (fun t =>
        -r * Real.sin t * d 0 (polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0) (r, t)) +
        r * Real.cos t * d 1 (polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0) (r, t)))
        2 (volume.restrict (Icc (-m65CrosscutAngle r) (m65CrosscutAngle r))) ∧
      (∀ s ∈ Icc (-m65CrosscutAngle r) (m65CrosscutAngle r),
        ∀ t ∈ Icc (-m65CrosscutAngle r) (m65CrosscutAngle r),
        v t - v s = ∫ a in s..t,
          -r * Real.sin a * d 0
            (polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0) (r, a)) +
          r * Real.cos a * d 1
            (polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0) (r, a))) ∧
      v (-m65CrosscutAngle r) = b (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r))) ∧
      v (m65CrosscutAngle r) = b (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) := by
  classical
  obtain ⟨f, A, B, C, hf, hA, hB, hC, hAlim, hBlim, hClim⟩ :=
    m65WeakTrace_exists_smooth_boundary_graph htrace
  let x : LoopPlane := -EuclideanSpace.basisFun (Fin 2) ℝ 0
  let mu := volume.restrict (Icc ε R)
  let nu := volume.restrict (Icc (-Real.pi) Real.pi)
  let Z : Lp ℝ 2 (volume.restrict loopDiskSet) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure LoopPlane) := zeroExtendL2 measurableSet_closedBall
  let T := polarPullbackL2 (E := ℝ) x R hε
  let D := polarAngularL2 x R hε
  let U (n : ℕ) := T (Z (A n))
  let V (n : ℕ) := D (fun i => Z (B n i))
  let U0 := T (Z u)
  let V0 := D (fun i => Z (d i))
  let J (w : Fin 2 → LoopPlane → ℝ) (p : ℝ × ℝ) :=
    -p.1 * Real.sin p.2 * w 0 (polarPlane x p) +
      p.1 * Real.cos p.2 * w 1 (polarPlane x p)
  have hcomp {g h : LoopPlane → ℝ} (heq : g =ᵐ[volume] h) :
      (fun p => g (polarPlane x p)) =ᵐ[mu.prod nu] fun p => h (polarPlane x p) :=
    ae_of_ae_map (polarPlane_measurePreserving x).measurable.aemeasurable
      (ae_mono (polarPlane_map_strip_le x hε)
        (Measure.ae_smul_measure heq (ENNReal.ofReal ε)⁻¹))
  have hZ (w : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      Z w =ᵐ[volume] loopDiskSet.indicator (w : LoopPlane → ℝ) :=
    zeroExtendL2_coe measurableSet_closedBall w
  have hZA (n : ℕ) : Z (A n) =ᵐ[volume] loopDiskSet.indicator (f n) :=
    (hZ (A n)).trans ((ae_eq_restrict_iff_indicator_ae_eq measurableSet_closedBall).mp (hA n))
  have hZB (n : ℕ) (i : Fin 2) : Z (B n i) =ᵐ[volume]
      loopDiskSet.indicator
        (fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
    (hZ (B n i)).trans
      ((ae_eq_restrict_iff_indicator_ae_eq measurableSet_closedBall).mp (hB n i))
  have hU (n : ℕ) : U n =ᵐ[mu.prod nu]
      fun p => loopDiskSet.indicator (f n) (polarPlane x p) :=
    (polarPullbackL2_ae x R hε (Z (A n))).trans (hcomp (hZA n))
  have hU0 : U0 =ᵐ[mu.prod nu]
      fun p => loopDiskSet.indicator (u : LoopPlane → ℝ) (polarPlane x p) :=
    (polarPullbackL2_ae x R hε (Z u)).trans (hcomp (hZ u))
  have hV (n : ℕ) : V n =ᵐ[mu.prod nu] fun p =>
      if polarPlane x p ∈ loopDiskSet then deriv (fun t => f n (polarPlane x (p.1, t))) p.2
        else 0 := by
    filter_upwards [polarAngularL2_ae x R hε (fun i => Z (B n i)),
      hcomp (hZB n 0), hcomp (hZB n 1)] with p hp h0 h1
    rw [hp, h0, h1]
    by_cases hi : polarPlane x p ∈ loopDiskSet
    · rw [if_pos hi, indicator_of_mem hi, indicator_of_mem hi,
        m65Crosscut_deriv (f n) ((hf n).of_le (by simp))]
    · simp only [if_neg hi, indicator_of_notMem hi, mul_zero, add_zero]
  have hV0 : V0 =ᵐ[mu.prod nu] fun p =>
      if polarPlane x p ∈ loopDiskSet then J (fun i => (d i : LoopPlane → ℝ)) p else 0 := by
    filter_upwards [polarAngularL2_ae x R hε (fun i => Z (d i)),
      hcomp (hZ (d 0)), hcomp (hZ (d 1))] with p hp h0 h1
    rw [hp, h0, h1]
    by_cases hi : polarPlane x p ∈ loopDiskSet
    · simp only [if_pos hi, indicator_of_mem hi, J]
    · simp only [if_neg hi, indicator_of_notMem hi, mul_zero, add_zero]
  have hUlim : Tendsto U atTop (𝓝 U0) :=
    (T.continuous.tendsto (Z u)).comp ((Z.continuous.tendsto u).comp hAlim)
  have hVlim : Tendsto V atTop (𝓝 V0) :=
    (D.continuous.tendsto (fun i => Z (d i))).comp
      (tendsto_pi_nhds.mpr fun i => (Z.continuous.tendsto (d i)).comp (hBlim i))
  let P := m65CrosscutBoundaryL2 hε hR (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
  let N := m65CrosscutBoundaryL2 hε hR (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
  have hP (n : ℕ) : P (C n) =ᵐ[mu]
      fun r => f n (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) := by
    simpa only [one_mul] using m65CrosscutBoundaryL2_ae_of_ae hε hR
      (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) (C n) (f n) (hC n)
  have hP0 : P b =ᵐ[mu]
      fun r => b (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) := by
    simpa only [one_mul] using m65CrosscutBoundaryL2_coe hε hR
      (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) b
  have hN (n : ℕ) : N (C n) =ᵐ[mu]
      fun r => f n (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r))) := by
    simpa only [neg_one_mul] using m65CrosscutBoundaryL2_ae_of_ae hε hR
      (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) (C n) (f n) (hC n)
  have hN0 : N b =ᵐ[mu]
      fun r => b (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r))) := by
    simpa only [neg_one_mul] using m65CrosscutBoundaryL2_coe hε hR
      (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) b
  obtain ⟨κ, hκ, hPpoint⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((P.continuous.tendsto b).comp hClim)).exists_seq_tendsto_ae
  obtain ⟨ell, hell, hNpoint⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((N.continuous.tendsto b).comp hClim).comp hκ.tendsto_atTop)).exists_seq_tendsto_ae
  have hkl := hκ.comp hell
  obtain ⟨σ, hσ, hUslice⟩ := m65L2_exists_slice_subsequence (hUlim.comp hkl.tendsto_atTop)
  obtain ⟨τ, hτ, hVslice⟩ :=
    m65L2_exists_slice_subsequence (hVlim.comp ((hkl.comp hσ).tendsto_atTop))
  have hUa : ∀ᵐ r ∂mu, ∀ n, ∀ᵐ t ∂nu,
      U n (r, t) = loopDiskSet.indicator (f n) (polarPlane x (r, t)) :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hU n))
  have hVa : ∀ᵐ r ∂mu, ∀ n, ∀ᵐ t ∂nu,
      V n (r, t) = if polarPlane x (r, t) ∈ loopDiskSet
        then deriv (fun a => f n (polarPlane x (r, a))) t else 0 :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hV n))
  filter_upwards [hUslice, hVslice, hUa, hVa, Measure.ae_ae_of_ae_prod hU0,
    Measure.ae_ae_of_ae_prod hV0, hPpoint, hNpoint, ae_all_iff.mpr hP,
    ae_all_iff.mpr hN, hP0, hN0, ae_restrict_mem measurableSet_Icc]
    with r hUr hVr hUar hVar hU0r hV0r hPr hNr hPar hNar hP0r hN0r hr
  have hrpos : 0 < r := hε.trans_le hr.1
  have hr1 : r ≤ 1 := hr.2.trans hR
  let c := m65CrosscutAngle r
  have hcpos : 0 < c := Real.arccos_pos.mpr (by linarith)
  have hsub : Icc (-c) c ⊆ Icc (-Real.pi) Real.pi := by
    intro t ht
    have hcpi := Real.arccos_le_pi (r / 2)
    exact ⟨by dsimp only [c, m65CrosscutAngle] at ht; linarith [ht.1],
      by dsimp only [c, m65CrosscutAngle] at ht; linarith [ht.2]⟩
  let rho := volume.restrict (Icc (-c) c)
  have hle : rho ≤ nu := Measure.restrict_mono hsub le_rfl
  let L : Lp ℝ 2 nu →L[ℝ] Lp ℝ 2 rho :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      (by simpa only [one_smul] using hle)
  have hL (w : Lp ℝ 2 nu) : L w =ᵐ[rho] w :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ _ w
  obtain ⟨hUn, hUzero, hUconv⟩ := hUr
  obtain ⟨hVn, hVzero, hVconv⟩ := hVr
  let inds (n : ℕ) := κ (ell (σ (τ n)))
  let uN (n : ℕ) := L ((hUn (τ n)).toLp (fun t => U (inds n) (r, t)))
  let dN (n : ℕ) := L ((hVn n).toLp (fun t => V (inds n) (r, t)))
  let uZ := L (hUzero.toLp (fun t => U0 (r, t)))
  let dZ := L (hVzero.toLp (fun t => V0 (r, t)))
  have hinside (t : ℝ) (ht : t ∈ Icc (-c) c) : polarPlane x (r, t) ∈ loopDiskSet :=
    m65Crosscut_mem_disk hrpos hr1 ht
  have huN (n : ℕ) : uN n =ᵐ[rho] fun t => f (inds n) (polarPlane x (r, t)) := by
    filter_upwards [hL _, ae_mono hle ((hUn (τ n)).coeFn_toLp.trans (hUar (inds n))),
      ae_restrict_mem measurableSet_Icc] with t ht he hi
    rw [ht]
    exact he.trans (indicator_of_mem (hinside t hi) _)
  have hdN (n : ℕ) : dN n =ᵐ[rho] deriv (fun t => f (inds n) (polarPlane x (r, t))) := by
    filter_upwards [hL _, ae_mono hle ((hVn n).coeFn_toLp.trans (hVar (inds n))),
      ae_restrict_mem measurableSet_Icc] with t ht he hi
    rw [ht]
    exact he.trans (if_pos (hinside t hi))
  have huZ : uZ =ᵐ[rho] fun t => u (polarPlane x (r, t)) := by
    filter_upwards [hL _, ae_mono hle (hUzero.coeFn_toLp.trans hU0r),
      ae_restrict_mem measurableSet_Icc] with t ht he hi
    rw [ht, he, indicator_of_mem (hinside t hi)]
  have hdZ : dZ =ᵐ[rho] fun t => J (fun i => (d i : LoopPlane → ℝ)) (r, t) := by
    filter_upwards [hL _, ae_mono hle (hVzero.coeFn_toLp.trans hV0r),
      ae_restrict_mem measurableSet_Icc] with t ht he hi
    rw [ht, he, if_pos (hinside t hi)]
  have hfunc (n : ℕ) : ContDiff ℝ 1 (fun t => f (inds n) (polarPlane x (r, t))) := by
    have hc : ContDiff ℝ 1 (fun t => polarPlane x (r, t)) :=
      contDiff_const.add ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).const_smul r)
    exact ((hf (inds n)).of_le (by simp)).comp hc
  obtain ⟨v, hvAC, hvAE, hvint, hvpoint⟩ := m65Interval_AC_graph_endpoint_limit
    (show -c < c by linarith) (fun n t => f (inds n) (polarPlane x (r, t))) hfunc
      uN dN uZ dZ huN hdN
      ((L.continuous.tendsto _).comp (hUconv.comp hτ.tendsto_atTop))
      ((L.continuous.tendsto _).comp hVconv)
  refine ⟨v, hvAC, hvAE.trans huZ, (Lp.memLp dZ).ae_eq hdZ, ?_, ?_, ?_⟩
  · intro s hs t ht
    rw [hvint s hs t ht]
    apply intervalIntegral.integral_congr_ae_restrict
    exact ae_restrict_of_ae_restrict_of_subset
      ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hs ht)) hdZ
  · have he := m65Crosscut_endpoint hrpos hr1 (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
    simp only [neg_one_mul] at he
    have ht := hvpoint (-c) ⟨le_rfl, by linarith⟩
    have he' : polarPlane x (r, -c) = Proofs.M58.angularPoint (-(2 * c)) := he
    rw [he'] at ht
    have hbconv := hNr.comp ((hσ.comp hτ).tendsto_atTop)
    rw [hN0r] at hbconv
    apply tendsto_nhds_unique ht
    exact hbconv.congr (fun n => hNar (inds n))
  · have he := m65Crosscut_endpoint hrpos hr1 (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
    simp only [one_mul] at he
    have ht := hvpoint c ⟨by linarith, le_rfl⟩
    have he' : polarPlane x (r, c) = Proofs.M58.angularPoint (2 * c) := he
    rw [he'] at ht
    have hbconv := hPr.comp ((hell.comp (hσ.comp hτ)).tendsto_atTop)
    rw [hP0r] at hbconv
    apply tendsto_nhds_unique ht
    exact hbconv.congr (fun n => hPar (inds n))

end PoincareConjecture
