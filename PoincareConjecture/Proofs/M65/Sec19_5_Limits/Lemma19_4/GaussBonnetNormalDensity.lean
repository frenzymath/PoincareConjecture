import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetHessian
import PoincareConjecture.Proofs.M03.MetricCompactBounds











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Topology ContDiff Manifold BigOperators

namespace PoincareConjecture.M65Gauss

open M65Branch

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}




def normalHessian (D : LeviCivitaData g)
    (F : LoopPlane → EuclideanSpace ℝ (Fin n)) (x u v : LoopPlane) :
    EuclideanSpace ℝ (Fin n) :=
  covariantHessianMap D F x u v -
    conformalTangentProjection g F x (covariantHessianMap D F x u v)




theorem normalHessian_eq_projection_derivative (D : LeviCivitaData g)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hconf : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, 0 < c ∧
      m60AreaGram g F y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (u v : LoopPlane) :
    normalHessian D F x u v =
      fderiv ℝ (conformalTangentProjection g F) x u (fderiv ℝ F x v) +
        connectionCoefficient D (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) -
          conformalTangentProjection g F x
            (connectionCoefficient D (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)) := by
  obtain ⟨c, hc, hx⟩ := hconf.self_of_nhds
  have h00 : g.inner (F x) (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = c := by
    have hh := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G 0 0) hx
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] using! hh
  have hP := differentiableAt_conformalTangentProjection hF (h00.trans_ne hc.ne')
  have hfix : ∀ᶠ y in 𝓝 x,
      conformalTangentProjection g F y (fderiv ℝ F y v) = fderiv ℝ F y v := by
    filter_upwards [hconf] with y hy
    obtain ⟨d, hd, hy⟩ := hy
    exact conformalTangentProjection_fixes hd hy v
  have hn := normal_second_derivative_eq_projection_derivative hP
    (show ContDiffAt ℝ 2 F x from hF.of_le (WithTop.coe_le_coe.mpr le_top)) u v hfix
  rw [normalHessian, covariantHessianMap, map_add, ← hn]
  abel




theorem norm_normalHessian_le_projection_derivative (D : LeviCivitaData g)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hconf : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, 0 < c ∧
      m60AreaGram g F y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (u v : LoopPlane) :
    ‖normalHessian D F x u v‖ ≤
      ‖fderiv ℝ (conformalTangentProjection g F) x u‖ * ‖fderiv ℝ F x v‖ +
        (1 + ‖conformalTangentProjection g F x‖) * ‖connectionCoefficient D (F x)‖ *
          ‖fderiv ℝ F x u‖ * ‖fderiv ℝ F x v‖ := by
  let P := conformalTangentProjection g F x
  let Q := fderiv ℝ (conformalTangentProjection g F) x u
  let C := connectionCoefficient D (F x)
  let a := fderiv ℝ F x u
  let b := fderiv ℝ F x v
  rw [normalHessian_eq_projection_derivative D hF hconf]
  change ‖Q b + C a b - P (C a b)‖ ≤
    ‖Q‖ * ‖b‖ + (1 + ‖P‖) * ‖C‖ * ‖a‖ * ‖b‖
  calc
    _ ≤ ‖Q b‖ + ‖C a b‖ + ‖P (C a b)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖Q‖ * ‖b‖ + ‖C‖ * ‖a‖ * ‖b‖ + ‖P‖ * (‖C‖ * ‖a‖ * ‖b‖) := by
      apply add_le_add
      · exact add_le_add (Q.le_opNorm b) (C.le_opNorm₂ a b)
      · exact (P.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (C.le_opNorm₂ a b) (norm_nonneg _))
    _ = _ := by ring




theorem normalHessian_density_le (D : LeviCivitaData g)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {x : LoopPlane}
    (hF : ContDiffAt ℝ ∞ F x)
    (hconf : ∀ᶠ y in 𝓝 x, ∃ c : ℝ, 0 < c ∧
      m60AreaGram g F y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {lam c C : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hC : 0 ≤ C)
    (hx : m60AreaGram g F x = lam • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hmetric : ∀ v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤ g.inner (F x) v v ∧
      g.inner (F x) v v ≤ C * ‖v‖ ^ 2)
    (i j : Fin 2) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    let B := normalHessian D F x (e i) (e j)
    g.inner (F x) B B / lam ≤
      (2 * C / c) * ‖fderiv ℝ (conformalTangentProjection g F) x (e i)‖ ^ 2 +
        (2 * C / c ^ 2) * (1 + ‖conformalTangentProjection g F x‖) ^ 2 *
          ‖connectionCoefficient D (F x)‖ ^ 2 * lam := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let a := ‖fderiv ℝ F x (e i)‖
  let b := ‖fderiv ℝ F x (e j)‖
  let q := ‖fderiv ℝ (conformalTangentProjection g F) x (e i)‖
  let k := (1 + ‖conformalTangentProjection g F x‖) * ‖connectionCoefficient D (F x)‖
  let B := normalHessian D F x (e i) (e j)
  have hcol (l : Fin 2) : g.inner (F x) (fderiv ℝ F x (e l))
      (fderiv ℝ F x (e l)) = lam := by
    have hh := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G l l) hx
    simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, e] using! hh
  have ha : a ^ 2 ≤ lam / c := (le_div_iff₀ hc).mpr (by
    simpa only [mul_comm c, ← hcol i] using (hmetric (fderiv ℝ F x (e i))).1)
  have hb : b ^ 2 ≤ lam / c := (le_div_iff₀ hc).mpr (by
    simpa only [mul_comm c, ← hcol j] using (hmetric (fderiv ℝ F x (e j))).1)
  have han : 0 ≤ a := norm_nonneg _
  have hbn : 0 ≤ b := norm_nonneg _
  have hqn : 0 ≤ q := norm_nonneg _
  have hkn : 0 ≤ k := by dsimp only [k]; positivity
  have hB := norm_normalHessian_le_projection_derivative D hF hconf (e i) (e j)
  change ‖B‖ ≤ q * b + k * a * b at hB
  have hB2 : ‖B‖ ^ 2 ≤ 2 * q ^ 2 * b ^ 2 + 2 * k ^ 2 * a ^ 2 * b ^ 2 := by
    have hs := sq_le_sq₀ (norm_nonneg B) (by positivity : 0 ≤ q * b + k * a * b) |>.mpr hB
    nlinarith [sq_nonneg (q * b - k * a * b)]
  have hab : a ^ 2 * b ^ 2 ≤ (lam / c) ^ 2 := by
    calc
      _ ≤ (lam / c) * (lam / c) := mul_le_mul ha hb (sq_nonneg b) (by positivity)
      _ = _ := by ring
  have hB3 : ‖B‖ ^ 2 ≤ 2 * q ^ 2 * (lam / c) + 2 * k ^ 2 * (lam / c) ^ 2 := by
    apply hB2.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hb (by positivity))
      (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hab
          (by positivity : 0 ≤ 2 * k ^ 2))
  change g.inner (F x) B B / lam ≤ _
  calc
    _ ≤ (C * ‖B‖ ^ 2) / lam := div_le_div_of_nonneg_right (hmetric B).2 hlam.le
    _ ≤ (C * (2 * q ^ 2 * (lam / c) + 2 * k ^ 2 * (lam / c) ^ 2)) / lam :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB3 hC) hlam.le
    _ = _ := by
      dsimp only [q, k, e]
      field_simp [hc.ne', hlam.ne']





theorem normalHessian_density_integrableOn (D : LeviCivitaData g)
    {F : LoopPlane → EuclideanSpace ℝ (Fin n)} {K U : Set LoopPlane}
    {lam : LoopPlane → ℝ}
    {P : LoopPlane → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hK : IsCompact K) (hU : IsOpen U) (hF : ContinuousOn F K)
    (hFs : ContDiffOn ℝ ∞ F U) (hlam : ContinuousOn lam K)
    (hconf : ∀ x ∈ U, 0 < lam x ∧
      m60AreaGram g F x = lam x • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hP : ContinuousOn P K) (hPeq : ∀ x ∈ U, P x = conformalTangentProjection g F x)
    (i j : Fin 2)
    (hDP : MemLp (fun x => fderiv ℝ P x (EuclideanSpace.basisFun (Fin 2) ℝ i))
      2 (volume.restrict (K ∩ U))) :
    IntegrableOn (fun x =>
      let B := normalHessian D F x (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j)
      g.inner (F x) B B / lam x) (K ∩ U) volume := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let N := fun x => normalHessian D F x (e i) (e j)
  have hG : ContinuousOn (fun x => g.euclideanCoefficients (F x)) K :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous.comp_continuousOn hF
  obtain ⟨c, C, hc, hC, hmetric⟩ := Proofs.M03.exists_pos_uniform_bilinear_bounds hK hG
    (fun x _ v hv => g.pos (F x) v hv)
  have hlocal (x : LoopPlane) (hx : x ∈ U) : ∀ᶠ y in 𝓝 x, ∃ d : ℝ, 0 < d ∧
      m60AreaGram g F y = d • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ⟨lam y, hconf y hy⟩
  have hN : ContinuousOn N U := by
    intro x hx
    have hs := hFs.contDiffAt (hU.mem_nhds hx)
    have hd := hs.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    have hdd := hd.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    have h00 : g.inner (F x) (fderiv ℝ F x (e 0)) (fderiv ℝ F x (e 0)) = lam x := by
      have hh := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G 0 0) (hconf x hx).2
      simpa +instances only [m60AreaGram, mfderiv_eq_fderiv, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, e] using! hh
    have hp := (differentiableAt_conformalTangentProjection hs
      (h00.trans_ne (hconf x hx).1.ne')).continuousAt
    have hh : ContinuousAt (fun y => covariantHessianMap D F y (e i) (e j)) x :=
      ((hdd.continuousAt.clm_apply continuousAt_const).clm_apply continuousAt_const).add
        ((((contDiff_connectionCoefficient D).continuous.continuousAt.comp
          hs.continuousAt).clm_apply
          (hd.continuousAt.clm_apply continuousAt_const)).clm_apply
            (hd.continuousAt.clm_apply continuousAt_const))
    exact (hh.sub (hp.clm_apply hh)).continuousWithinAt
  have hKU : MeasurableSet (K ∩ U) := hK.measurableSet.inter hU.measurableSet
  have hmeas : AEStronglyMeasurable (fun x => g.inner (F x) (N x) (N x) / lam x)
      (volume.restrict (K ∩ U)) :=
    ((((hG.mono inter_subset_left).clm_apply (hN.mono inter_subset_right)).clm_apply
      (hN.mono inter_subset_right)).div (hlam.mono inter_subset_left)
        (fun x hx => (hconf x hx.2).1.ne')).aestronglyMeasurable hKU
  have hGamma : ContinuousOn (fun x => connectionCoefficient D (F x)) K :=
    (contDiff_connectionCoefficient D).continuous.comp_continuousOn hF
  obtain ⟨CP, hCP⟩ := hK.exists_bound_of_continuousOn hP
  obtain ⟨CG, hCG⟩ := hK.exists_bound_of_continuousOn
    (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) hGamma
  let weight : LoopPlane → ℝ := fun x =>
    ((2 * C / c ^ 2) * (1 + max CP 0) ^ 2 * (max CG 0) ^ 2) * lam x
  have hw : IntegrableOn weight K volume :=
    (hlam.const_mul _).integrableOn_compact hK
  have hmajor : Integrable (fun x => (2 * C / c) * ‖fderiv ℝ P x (e i)‖ ^ 2 + weight x)
      (volume.restrict (K ∩ U)) :=
    ((hDP.integrable_norm_pow (p := 2) (by norm_num)).const_mul _).add
      (hw.mono_set inter_subset_left)
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem hKU] with x hx
  have hnonneg : 0 ≤ g.inner (F x) (N x) (N x) / lam x :=
    div_nonneg ((mul_nonneg hc.le (sq_nonneg _)).trans (hmetric x hx.1 (N x)).1)
      (hconf x hx.2).1.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hbound := normalHessian_density_le D (hFs.contDiffAt (hU.mem_nhds hx.2))
    (hlocal x hx.2) (hconf x hx.2).1 hc hC.le (hconf x hx.2).2 (hmetric x hx.1) i j
  have heq : P =ᶠ[𝓝 x] conformalTangentProjection g F := by
    filter_upwards [hU.mem_nhds hx.2] with y hy
    exact hPeq y hy
  rw [← heq.fderiv_eq (𝕜 := ℝ), ← hPeq x hx.2] at hbound
  apply hbound.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (hconf x hx.2).1.le
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl
      ((hCP x hx.1).trans (le_max_left CP 0))) 2
  · exact pow_le_pow_left₀ (norm_nonneg _) ((hCG x hx.1).trans (le_max_left _ _)) 2
  · positivity
  · positivity

end PoincareConjecture.M65Gauss
