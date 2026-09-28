import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalization
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace SchwartzMap ContDiff LineDeriv

namespace PoincareConjecture.M65Euler

open DeTurckDomainRegularityNative EuclideanMollificationNative

private def vectorL2 {N : ℕ} (u : Fin N → Lp ℝ 2 (volume : Measure LoopPlane)) :
    Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane) :=
  ∑ j, (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun (Fin N) ℝ j)).compLp
    (u j)

private theorem vectorL2_ae {N : ℕ}
    (u : Fin N → Lp ℝ 2 (volume : Measure LoopPlane)) :
    vectorL2 u =ᵐ[volume] fun z => WithLp.toLp 2 (fun j => u j z) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j =>
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun (Fin N) ℝ j)).compLp
      (u j)), ae_all_iff.mpr (fun j =>
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun (Fin N) ℝ j)).coeFn_compLp
      (u j))] with z hz hj
  rw [vectorL2, hz]
  simp only [Finset.sum_apply, hj, ContinuousLinearMap.toSpanSingleton_apply]
  exact (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (WithLp.toLp 2 (fun j => u j z))

private theorem vectorL2_tendsto {N : ℕ}
    {u : ℕ → Fin N → Lp ℝ 2 (volume : Measure LoopPlane)}
    {u0 : Fin N → Lp ℝ 2 (volume : Measure LoopPlane)}
    (hu : ∀ j, Tendsto (fun n => u n j) atTop (𝓝 (u0 j))) :
    Tendsto (fun n => vectorL2 (u n)) atTop (𝓝 (vectorL2 u0)) := by
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun (Fin N) ℝ j)).compLpL
    2 (volume : Measure LoopPlane)).continuous.tendsto (u0 j) |>.comp (hu j)

private theorem vectorL2_coordinates {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)) :
    vectorL2 (fun j =>
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp u) = u := by
  apply Lp.ext
  filter_upwards [vectorL2_ae (fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp u),
    ae_all_iff.mpr (fun j =>
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).coeFn_compLp u)] with z hz hj
  rw [hz]
  ext j
  exact hj j

private theorem vector_mollified_graph {N : ℕ}
    (u d : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)) (v : LoopPlane)
    (hweak : ∀ j (φ : 𝓢(LoopPlane, ℝ)),
      ⟪(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp d,
        φ.toLp 2 volume⟫_ℝ = -(∫ z, u z j * fderiv ℝ φ z v)) :
    ∃ (f : ℕ → LoopPlane → EuclideanSpace ℝ (Fin N))
      (U D : ℕ → Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, U n =ᵐ[volume] f n) ∧
      (∀ n, D n =ᵐ[volume] fun z => fderiv ℝ (f n) z v) ∧
      Tendsto U atTop (𝓝 u) ∧ Tendsto D atTop (𝓝 d) := by
  let uc (j : Fin N) := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp u
  let dc (j : Fin N) := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp d
  let eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have heps (n : ℕ) : 0 < eps n := by dsimp only [eps]; positivity
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let B := EuclideanSpace.basisFun (Fin N) ℝ
  let f (n : ℕ) (z : LoopPlane) := ∑ j, mollify (heps n) (uc j) z • B j
  let U (n : ℕ) := vectorL2 (fun j => mollifyL2 (heps n) (uc j))
  let D (n : ℕ) := vectorL2 (fun j => mollifyL2 (heps n) (dc j))
  have huc (j : Fin N) : uc j =ᵐ[volume] fun z => u z j :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).coeFn_compLp u
  have hw (j : Fin N) (φ : 𝓢(LoopPlane, ℝ)) :
      ⟪dc j, φ.toLp 2 volume⟫_ℝ = -(∫ z, uc j z * fderiv ℝ φ z v) := by
    rw [hweak j φ]
    congr 1
    exact integral_congr_ae (by
      filter_upwards [huc j] with z hz
      rw [hz])
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    ContDiff.sum (fun j _ => (contDiff_mollify (heps n) (uc j)).smul contDiff_const)
  have hD (n : ℕ) (z : LoopPlane) : fderiv ℝ (f n) z v =
      ∑ j, mollify (heps n) (dc j) z • B j := by
    dsimp only [f]
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => mollify (heps n) (uc j) z • B j) (fun j _ =>
      ((contDiff_mollify (heps n) (uc j)).differentiable (by simp) z).smul
        (differentiableAt_const (B j)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_smul_const
      ((contDiff_mollify (heps n) (uc j)).differentiable (by simp) z)]
    simp only [ContinuousLinearMap.smulRight_apply]
    rw [fderiv_mollify_of_weak_pairing (heps n) (uc j) (dc j) v (hw j) z]
  refine ⟨f, U, D, hf, ?_, ?_, ?_, ?_⟩
  · intro n
    filter_upwards [vectorL2_ae (fun j => mollifyL2 (heps n) (uc j)),
      ae_all_iff.mpr (fun j => mollifyL2_ae_eq (heps n) (uc j))] with z hz hj
    rw [hz]
    change WithLp.toLp 2 (fun j => mollifyL2 (heps n) (uc j) z) = _
    simp only [hj]
    exact (B.sum_repr (WithLp.toLp 2 (fun j => mollify (heps n) (uc j) z))).symm
  · intro n
    filter_upwards [vectorL2_ae (fun j => mollifyL2 (heps n) (dc j)),
      ae_all_iff.mpr (fun j => mollifyL2_ae_eq (heps n) (dc j))] with z hz hj
    rw [hz, hD]
    simp only [hj]
    exact (B.sum_repr (WithLp.toLp 2 (fun j => mollify (heps n) (dc j) z))).symm
  · have h := vectorL2_tendsto (fun j => tendsto_mollifyL2 eps heps heps0 (uc j))
    simpa only [uc, vectorL2_coordinates] using h
  · have h := vectorL2_tendsto (fun j => tendsto_mollifyL2 eps heps heps0 (dc j))
    simpa only [dc, vectorL2_coordinates] using h

private theorem coefficientL2_tendsto_varying {N : ℕ}
    {A : ℕ → LoopPlane → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    {A0 : LoopPlane → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hA : ∀ n, AEStronglyMeasurable (A n) volume)
    (hA0 : AEStronglyMeasurable A0 volume) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ z ∂volume, ‖A n z‖ ≤ C)
    (hb0 : ∀ᵐ z ∂volume, ‖A0 z‖ ≤ C)
    (hlim : ∀ᵐ z ∂volume, Tendsto (fun n => A n z) atTop (𝓝 (A0 z)))
    {d : ℕ → Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)}
    {d0 : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)}
    (hd : Tendsto d atTop (𝓝 d0)) :
    Tendsto (fun n => Lp.coefficientL2 (A n) (hA n) C (hb n) (d n)) atTop
      (𝓝 (Lp.coefficientL2 A0 hA0 C hb0 d0)) := by
  let T (n : ℕ) := Lp.coefficientL2 (A n) (hA n) C (hb n)
  have hsmall : Tendsto (fun n => T n (d n - d0)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => C * ‖d n - d0‖)
    · exact Eventually.of_forall fun n => Lp.norm_le_mul_norm_of_ae_le_mul (by
        filter_upwards [Lp.coefficientL2_ae (A n) (hA n) C (hb n) (d n - d0), hb n]
          with z hz hbz
        rw [hz]
        exact ((A n z).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hbz (norm_nonneg _)))
    · simpa only [sub_self, norm_zero, mul_zero] using
        (hd.sub (tendsto_const_nhds (x := d0))).norm.const_mul C
  have hfixed := Lp.tendsto_coefficientL2_apply hA hA0 hC hb hb0 hlim d0
  simpa only [T, map_sub, sub_add_cancel, zero_add] using hsmall.add hfixed

set_option maxHeartbeats 1600000 in





theorem weak_chain {N : ℕ}
    (u d : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)) (v : LoopPlane)
    (hweak : ∀ j (φ : 𝓢(LoopPlane, ℝ)),
      ⟪(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp d,
        φ.toLp 2 volume⟫_ℝ = -(∫ z, u z j * fderiv ℝ φ z v))
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (hh : ContDiff ℝ 1 h) (hzero : h 0 = 0)
    (C : NNReal) (hbound : ∀ x, ‖fderiv ℝ h x‖ ≤ (C : ℝ)) :
    ∃ U D : Lp ℝ 2 (volume : Measure LoopPlane),
      (U =ᵐ[volume] fun z => h (u z)) ∧
      (D =ᵐ[volume] fun z => fderiv ℝ h (u z) (d z)) ∧
      ∀ φ : 𝓢(LoopPlane, ℝ),
        ⟪D, φ.toLp 2 volume⟫_ℝ = -(∫ z, U z * fderiv ℝ φ z v) := by
  have hLip : LipschitzWith C h := lipschitzWith_of_nnnorm_fderiv_le
    (hh.differentiable one_ne_zero) (fun x => hbound x)
  have hDh : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  let U0 := hLip.compLp hzero u
  let A0 (z : LoopPlane) := fderiv ℝ h (u z)
  have hA0 : AEStronglyMeasurable A0 volume :=
    hDh.comp_aestronglyMeasurable (Lp.memLp u).1
  have hb0 : ∀ᵐ z ∂volume, ‖A0 z‖ ≤ C := ae_of_all _ fun z => hbound _
  let D0 := Lp.coefficientL2 A0 hA0 C hb0 d
  have hU0 : U0 =ᵐ[volume] fun z => h (u z) := hLip.coeFn_compLp hzero u
  have hD0 : D0 =ᵐ[volume] fun z => fderiv ℝ h (u z) (d z) :=
    Lp.coefficientL2_ae A0 hA0 C hb0 d
  refine ⟨U0, D0, hU0, hD0, ?_⟩
  obtain ⟨f, U, D, hf, hU, hD, hUlim, hDlim⟩ := vector_mollified_graph u d v hweak
  obtain ⟨sigma, hsigma, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hUlim).exists_seq_tendsto_ae
  have hpoint : ∀ᵐ z ∂volume, Tendsto (fun n => f (sigma n) z) atTop (𝓝 (u z)) := by
    filter_upwards [hae, ae_all_iff.mpr hU] with z hz hUz
    simpa only [hUz] using hz
  let A (n : ℕ) (z : LoopPlane) := fderiv ℝ h (f (sigma n) z)
  have hA (n : ℕ) : AEStronglyMeasurable (A n) volume :=
    (hDh.comp (hf (sigma n)).continuous).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂volume, ‖A n z‖ ≤ C := ae_of_all _ fun z => hbound _
  let V (n : ℕ) := hLip.compLp hzero (U (sigma n))
  let W (n : ℕ) := Lp.coefficientL2 (A n) (hA n) C (hb n) (D (sigma n))
  have hV (n : ℕ) : V n =ᵐ[volume] fun z => h (f (sigma n) z) := by
    filter_upwards [hLip.coeFn_compLp hzero (U (sigma n)), hU (sigma n)] with z hz hfz
    rw [hz, Function.comp_apply, hfz]
  have hW (n : ℕ) : W n =ᵐ[volume] fun z =>
      fderiv ℝ (fun z => h (f (sigma n) z)) z v := by
    filter_upwards [Lp.coefficientL2_ae (A n) (hA n) C (hb n) (D (sigma n)),
      hD (sigma n)] with z hz hfz
    rw [hz, hfz]
    rw [fderiv_fun_comp z (hh.differentiable one_ne_zero _)
      ((hf (sigma n)).differentiable (by simp) z)]
    rfl
  have hVlim : Tendsto V atTop (𝓝 U0) :=
    (hLip.continuous_compLp hzero).tendsto u |>.comp (hUlim.comp hsigma.tendsto_atTop)
  have hcoef : ∀ᵐ z ∂volume, Tendsto (fun n => A n z) atTop (𝓝 (A0 z)) := by
    filter_upwards [hpoint] with z hz
    exact (hDh.tendsto (u z)).comp hz
  have hWlim : Tendsto W atTop (𝓝 D0) := coefficientL2_tendsto_varying hA hA0
    C.coe_nonneg hb hb0 hcoef (hDlim.comp hsigma.tendsto_atTop)
  intro φ
  have hpair (n : ℕ) : ⟪W n, φ.toLp 2 volume⟫_ℝ =
      -⟪V n, (∂_{v} φ).toLp 2 volume⟫_ℝ := by
    let g (z : LoopPlane) := h (f (sigma n) z)
    have hg : ContDiff ℝ 1 g := hh.comp ((hf (sigma n)).of_le (by simp))
    have hgL : MemLp g 2 volume := (Lp.memLp (V n)).ae_eq (hV n)
    have hdL : MemLp (fun z => fderiv ℝ g z v) 2 volume :=
      (Lp.memLp (W n)).ae_eq (hW n)
    have htestD : MemLp (fun z => fderiv ℝ φ z v) 2 volume := (∂_{v} φ).memLp 2 volume
    have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := g) (g := φ) (v := v)
      (hdL.integrable_mul (φ.memLp 2 volume))
      (hgL.integrable_mul htestD) (hgL.integrable_mul (φ.memLp 2 volume))
      (fun z _ => hg.differentiable one_ne_zero z) (fun z _ => φ.differentiableAt)
    rw [inner_schwartz, inner_schwartz]
    have hleft : (∫ z, W n z * φ z) = ∫ z, fderiv ℝ g z v * φ z := by
      apply integral_congr_ae
      filter_upwards [hW n] with z hz
      rw [hz]
    have hright : (∫ z, V n z * (∂_{v} φ) z) = ∫ z, g z * fderiv ℝ φ z v := by
      apply integral_congr_ae
      filter_upwards [hV n] with z hz
      rw [hz, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hleft, hright]
    linarith only [hi]
  have hout : ⟪D0, φ.toLp 2 volume⟫_ℝ = -⟪U0, (∂_{v} φ).toLp 2 volume⟫_ℝ :=
    tendsto_nhds_unique (hWlim.inner (𝕜 := ℝ) tendsto_const_nhds)
      (by simpa only [hpair] using (hVlim.inner (𝕜 := ℝ) (tendsto_const_nhds
        (x := (∂_{v} φ).toLp 2 volume))).neg)
  simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hout

end PoincareConjecture.M65Euler
