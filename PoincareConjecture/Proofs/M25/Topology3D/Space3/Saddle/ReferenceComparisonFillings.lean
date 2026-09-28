import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AngularReconnection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.EndpointReparametrization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PeriodicCurveSmooth
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology Matrix

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1500000 in

set_option linter.unusedVariables false in




theorem exists_nonnested_reference_comparison_fillings
    (hP : PlanarSchoenfliesService)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmuSmall : mu ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
    let Eta : Fin 2 → Set E2 := fun i => (F 1) '' Z i
    ∀ (nu : ℝ) (hnu : 0 < nu) (hnuSmall : nu < 1 / 16)
      (alpha : Fin 2 → ℝ → E2)
      (hAlpha : ∀ i,
        ContDiffOn ℝ ∞ (alpha i) (Ioo (-nu) (1 + nu)))
      (hAlphaInj : ∀ i, Set.InjOn (alpha i) (Ioo (-nu) (1 + nu)))
      (hAlphaReg : ∀ i, ∀ t ∈ Ioo (-nu) (1 + nu), deriv (alpha i) t ≠ 0)
      (hSign : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 < sign i * (J2 (alpha i t)).2)
      (hProper : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, 1 < ‖alpha i t‖)
      (hInitial : ∀ i t, |t| < nu →
        alpha i t = (1 + t) • port (ep (i, 0)))
      (hTerminal : ∀ i t, |t - 1| < nu →
        alpha i t = (2 - t) • port (ep (i, 1))),
      ∃ (c : Fin 2 → UnitCircle → E2)
        (B : Fin 2 → BallNeighborhoodChart E2 E2),
        (∀ i, IsPlanarEmbedding (c i)) ∧
        (∀ i, range (c i) = (alpha i '' Icc (0 : ℝ) 1) ∪ Eta i) ∧
        (∀ i, (B i).boundary = range (c i)) ∧
        (∀ i, (B i).closedRegion ⊆ {x : E2 | 0 < sign i * (J2 x).2}) ∧
        Disjoint (B 0).closedRegion (B 1).closedRegion := by
  classical
  dsimp only
  intro nu hnu hnuSmall alpha hAlpha hAlphaInj hAlphaReg hSign hProper hInitial hTerminal
  let F := Classical.choose (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a => J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let sign : Fin 2 → ℝ := ![1, -1]
  let Z : Fin 2 → Set E2 := fun i =>
    {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
  let Eta : Fin 2 → Set E2 := fun i => (F 1) '' Z i
  let X : ℝ → ℝ → Fin 4 → E2 := fun a r i =>
    J2.symm (sx i * Real.sqrt ((r ^ 2 + a) / 2), sy i * Real.sqrt ((r ^ 2 - a) / 2))
  change ∀ i t, |t| < nu → alpha i t = (1 + t) • port (ep (i, 0)) at hInitial
  change ∀ i t, |t - 1| < nu → alpha i t = (2 - t) • port (ep (i, 1)) at hTerminal
  change ∀ i t, t ∈ Icc (0 : ℝ) 1 → 0 < sign i * (J2 (alpha i t)).2 at hSign
  have hFspec := Classical.choose_spec (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  dsimp only at hFspec
  obtain ⟨hFa, hFb, hFform, hFn, hFs0, hFs1, hFC, hFsupp, hFX, hFsgn⟩ := hFspec
  clear hFa hFb hFform hFs0 hFs1 hFC hFsupp
  change ∀ t i r, r ∈ Icc (3 / 4 : ℝ) (5 / 4) →
    F t (X (-mu) r i) = X (-(1 - Real.smoothTransition t) * mu) r i at hFX
  have hsig (i : Fin 2) : (sign i) ^ 2 = 1 ∧ sign i ≠ 0 := by
    fin_cases i <;> norm_num [sign]
  have hlabels (i : Fin 2) : sx (ep (i, 0)) = sign i ∧ sx (ep (i, 1)) = -sign i ∧
      sy (ep (i, 0)) = sign i ∧ sy (ep (i, 1)) = sign i := by
    fin_cases i <;> norm_num [sx, sy, sign, ep, finProdFinEquiv]
  have hn (x y : ℝ) : ‖J2.symm (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    simpa only [J2.apply_symm_apply] using (hJ2 (J2.symm (x, y))).symm
  have hpNorm (a : Fin 4) : ‖port a‖ = 1 := by
    have hh := hn (sx a / Real.sqrt 2) (sy a / Real.sqrt 2)
    have hs : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by fin_cases a <;> norm_num [sx, sy]
    change ‖port a‖ ^ 2 = _ at hh
    rw [div_pow, div_pow, hs.1, hs.2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hh
    nlinarith [norm_nonneg (port a)]
  have hpNe (a : Fin 4) : port a ≠ 0 := by intro h; simpa [h] using hpNorm a
  have hXzero (r : ℝ) (hr : 0 < r) (a : Fin 4) : X 0 r a = r • port a := by
    have hs : Real.sqrt (r ^ 2 / 2) = r / Real.sqrt 2 := by
      rw [Real.sqrt_div (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]
    apply J2.injective
    simp only [X, port, add_zero, sub_zero, hs, map_smul, J2.apply_symm_apply,
      Prod.smul_mk, smul_eq_mul]
    congr 1 <;> ring
  have hmu1 : mu < 1 := by linarith
  have hmuGap : 0 < 1 - mu := sub_pos.mpr hmu1
  let s : ℝ := Real.sqrt ((1 - mu) / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hmuGap (by norm_num))
  have hs2 : s ^ 2 = (1 - mu) / 2 := Real.sq_sqrt (div_nonneg hmuGap.le (by norm_num))
  let v : ℝ → ℝ := fun t => (2 * t - 1) * s
  let z : Fin 2 → ℝ → E2 := fun i t =>
    J2.symm (sign i * v t, sign i * Real.sqrt ((v t) ^ 2 + mu))
  let R : ℝ → ℝ := fun t => Real.sqrt (2 * (v t) ^ 2 + mu)
  have hv : ContDiff ℝ ∞ v := by dsimp [v]; fun_prop
  have hrad (t : ℝ) : 0 < (v t) ^ 2 + mu := by positivity
  have hRrad (t : ℝ) : 0 < 2 * (v t) ^ 2 + mu := by positivity
  have hRootSmooth : ContDiff ℝ ∞ (fun t => Real.sqrt ((v t) ^ 2 + mu)) :=
    ((hv.pow 2).add contDiff_const).sqrt (fun t => (hrad t).ne')
  have hz (i : Fin 2) : ContDiff ℝ ∞ (z i) :=
    J2.symm.contDiff.comp ((contDiff_const.mul hv).prodMk
      (contDiff_const.mul hRootSmooth))
  have hR : ContDiff ℝ ∞ R :=
    ((contDiff_const.mul (hv.pow 2)).add contDiff_const).sqrt (fun t => (hRrad t).ne')
  have hRp (t : ℝ) : 0 < R t := Real.sqrt_pos.mpr (hRrad t)
  have hRsq (t : ℝ) : (R t) ^ 2 = 2 * (v t) ^ 2 + mu := Real.sq_sqrt (hRrad t).le
  have hRform (t : ℝ) : (R t) ^ 2 = mu + (1 - mu) * (2 * t - 1) ^ 2 := by
    rw [hRsq]; dsimp [v]; nlinarith [congrArg (fun q : ℝ => q * (2 * t - 1) ^ 2) hs2]
  have hzNorm (i : Fin 2) (t : ℝ) : ‖z i t‖ = R t := by
    have hh := hn (sign i * v t) (sign i * Real.sqrt ((v t) ^ 2 + mu))
    change ‖z i t‖ ^ 2 = _ at hh
    simp only [mul_pow, (hsig i).1, one_mul, Real.sq_sqrt (hrad t).le] at hh
    nlinarith [hRsq t, norm_nonneg (z i t), hRp t]
  have hRends : R 0 = 1 ∧ R 1 = 1 := by
    constructor <;> nlinarith [hRform 0, hRform 1, hRp 0, hRp 1]
  have hRle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : R t ≤ 1 := by
    have hq : (2 * t - 1) ^ 2 ≤ 1 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.1 (sub_nonpos.mpr ht.2)]
    nlinarith [hRform t, hRp t, mul_nonneg (sub_nonneg.mpr hmu1.le) (sub_nonneg.mpr hq)]
  have hRlt (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : R t < 1 := by
    have hq : (2 * t - 1) ^ 2 < 1 := by nlinarith [mul_neg_of_pos_of_neg ht.1 (sub_neg.mpr ht.2)]
    nlinarith [hRform t, hRp t, mul_pos (sub_pos.mpr hmu1) (sub_pos.mpr hq)]
  have hzInj (i : Fin 2) : Injective (z i) := by
    intro t u h
    have hh := congrArg (fun y : E2 => (J2 y).1) h
    simp only [z, J2.apply_symm_apply] at hh
    have hh' := mul_left_cancel₀ (hsig i).2 hh
    change (2 * t - 1) * s = (2 * u - 1) * s at hh'
    have hh'' := mul_right_cancel₀ hs.ne' hh'
    linarith
  have hzReg (i : Fin 2) (t : ℝ) : deriv (z i) t ≠ 0 := by
    intro hzero
    let L : E2 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp J2.toContinuousLinearMap
    have hcoord : L ∘ z i = fun x : ℝ => sign i * ((2 * x - 1) * s) := by
      funext x; simp [L, z, v]
    have hd : HasDerivAt (L ∘ z i) (sign i * (2 * s)) t := by
      rw [hcoord]
      have hlin : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t := by
        simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
      exact (hlin.mul_const s).const_mul (sign i)
    have he := fderiv_comp_deriv t L.differentiableAt (hz i |>.differentiable (by simp) t)
    rw [hd.deriv, hzero, map_zero] at he
    exact (mul_ne_zero (hsig i).2 (by positivity)) he
  have hzImage (i : Fin 2) : z i '' Icc (0 : ℝ) 1 = Z i := by
    ext x; constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨by rw [hzNorm]; exact hRle t ht, ?_⟩
      simp only [z, J2.apply_symm_apply, mul_pow, (hsig i).1, one_mul]
    · rintro ⟨hx, hy⟩
      have hq : 2 * (J2 x).1 ^ 2 + mu = ‖x‖ ^ 2 := by
        have hh := hJ2 x
        rw [hy, mul_pow, (hsig i).1, one_mul,
          Real.sq_sqrt (by positivity : 0 ≤ (J2 x).1 ^ 2 + mu)] at hh
        linarith
      have hb : -s ≤ sign i * (J2 x).1 ∧ sign i * (J2 x).1 ≤ s := by
        have hn2 : ‖x‖ ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx)]
        have hsx : (J2 x).1 ^ 2 ≤ s ^ 2 := by nlinarith [hs2]
        have habs := abs_le_of_sq_le_sq' hsx hs.le
        fin_cases i <;> norm_num [sign] <;> constructor <;> linarith [habs.1, habs.2]
      let t : ℝ := (sign i * (J2 x).1 / s + 1) / 2
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        have h0 : -1 ≤ sign i * (J2 x).1 / s := (le_div_iff₀ hs).mpr (by nlinarith [hb.1])
        have h1 : sign i * (J2 x).1 / s ≤ 1 := (div_le_iff₀ hs).mpr (by nlinarith [hb.2])
        dsimp [t]; constructor <;> linarith
      have hvt : v t = sign i * (J2 x).1 := by dsimp [v, t]; field_simp [hs.ne']; ring
      refine ⟨t, ht, J2.injective ?_⟩
      simp only [z, J2.apply_symm_apply, hvt, mul_pow, (hsig i).1, one_mul]
      apply Prod.ext
      · calc
          sign i * (sign i * (J2 x).1) = (sign i) ^ 2 * (J2 x).1 := by ring
          _ = (J2 x).1 := by rw [(hsig i).1, one_mul]
      · exact hy.symm
  have hRwindow (t : ℝ) (ht : |t| < 1 / 64 ∨ |t - 1| < 1 / 64) :
      R t ∈ Icc (3 / 4 : ℝ) (5 / 4) := by
    have hh : (31 / 32 : ℝ) ^ 2 < (2 * t - 1) ^ 2 ∧
        (2 * t - 1) ^ 2 < (33 / 32 : ℝ) ^ 2 := by
      rcases ht with ht | ht
      · rw [abs_lt] at ht
        constructor
        · nlinarith [mul_pos (by linarith [ht.2] : 0 < -(2 * t - 1) - 31 / 32)
            (by linarith [ht.2] : 0 < -(2 * t - 1) + 31 / 32)]
        · nlinarith [mul_pos (by linarith [ht.1] : 0 < 33 / 32 + (2 * t - 1))
            (by linarith [ht.2] : 0 < 33 / 32 - (2 * t - 1))]
      · rw [abs_lt] at ht
        constructor
        · nlinarith [mul_pos (by linarith [ht.1] : 0 < (2 * t - 1) - 31 / 32)
            (by linarith [ht.1] : 0 < (2 * t - 1) + 31 / 32)]
        · nlinarith [mul_pos (by linarith [ht.1] : 0 < 33 / 32 + (2 * t - 1))
            (by linarith [ht.2] : 0 < 33 / 32 - (2 * t - 1))]
    have hlo := mul_pos (sub_pos.mpr hmu1) (sub_pos.mpr hh.1)
    have hhi := mul_pos (sub_pos.mpr hmu1) (sub_pos.mpr hh.2)
    constructor <;> nlinarith [hRform t, hRp t]
  have hRootX (t : ℝ) : Real.sqrt (((R t) ^ 2 - mu) / 2) = |v t| := by
    rw [hRsq, show (2 * (v t) ^ 2 + mu - mu) / 2 = (v t) ^ 2 by ring,
      Real.sqrt_sq_eq_abs]
  have hRootY (t : ℝ) : Real.sqrt (((R t) ^ 2 + mu) / 2) = Real.sqrt ((v t) ^ 2 + mu) := by
    rw [hRsq]; congr 1; ring
  have hzLeft (i : Fin 2) (t : ℝ) (ht : |t| < 1 / 64) :
      z i t = X (-mu) (R t) (ep (i, 1)) := by
    have hvn : v t < 0 := mul_neg_of_neg_of_pos (by rw [abs_lt] at ht; linarith [ht.2]) hs
    apply J2.injective
    simp only [z, X, J2.apply_symm_apply, ← sub_eq_add_neg, sub_neg_eq_add,
      hRootX, hRootY, abs_of_neg hvn, (hlabels i).2.1, (hlabels i).2.2.2]
    congr 1; ring
  have hzRight (i : Fin 2) (t : ℝ) (ht : |t - 1| < 1 / 64) :
      z i t = X (-mu) (R t) (ep (i, 0)) := by
    have hvp : 0 < v t := mul_pos (by rw [abs_lt] at ht; linarith [ht.1]) hs
    apply J2.injective
    simp only [z, X, J2.apply_symm_apply, ← sub_eq_add_neg, sub_neg_eq_add,
      hRootX, hRootY, abs_of_pos hvp, (hlabels i).1, (hlabels i).2.2.1]
  have hFLeft (i : Fin 2) (t : ℝ) (ht : |t| < 1 / 64) :
      F 1 (z i t) = R t • port (ep (i, 1)) := by
    rw [hzLeft i t ht, hFX 1 _ _ (hRwindow t (Or.inl ht)),
      Real.smoothTransition.one]
    simpa using hXzero (R t) (hRp t) (ep (i, 1))
  have hFRight (i : Fin 2) (t : ℝ) (ht : |t - 1| < 1 / 64) :
      F 1 (z i t) = R t • port (ep (i, 0)) := by
    rw [hzRight i t ht, hFX 1 _ _ (hRwindow t (Or.inr ht)),
      Real.smoothTransition.one]
    simpa using hXzero (R t) (hRp t) (ep (i, 0))
  have hRd (t : ℝ) : HasDerivAt R (4 * s ^ 2 * (2 * t - 1) / R t) t := by
    have hvt : HasDerivAt v (2 * s) t := by
      have hlin : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t := by
        simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
      exact hlin.mul_const s
    have hh := (((hvt.pow 2).const_mul 2).add_const mu).sqrt (hRrad t).ne'
    apply hh.congr_deriv
    change 2 * (2 * v t ^ (2 - 1) * (2 * s)) / (2 * R t) = _
    norm_num only [Nat.reduceSub, pow_one]
    dsimp only [v]
    ring
  have hd0 : deriv (fun t => 1 - R t) 0 = 2 * (1 - mu) := by
    have hh := (hasDerivAt_const 0 (1 : ℝ) |>.sub (hRd 0)).deriv
    change deriv (fun t => 1 - R t) 0 = _ at hh
    rw [hh, hRends.1]
    nlinarith [hs2]
  have hd1 : deriv R 1 = 2 * (1 - mu) := by rw [(hRd 1).deriv, hRends.2]; nlinarith [hs2]
  obtain ⟨nuB, Theta, hnuB, hnuBsmall, hTheta⟩ :=
    exists_saddle_endpoint_reparametrizations 2 (1 / 64) (by norm_num) (by norm_num)
      (fun _ t => 1 - R t) (fun _ => R)
      (fun _ => (contDiff_const.sub hR).contDiffOn) (fun _ => hR.contDiffOn)
      (fun _ => by simp [hRends.1]) (fun _ => hRends.2)
      (fun _ => by rw [hd0]; positivity) (fun _ => by rw [hd1]; positivity)
  let beta : Fin 2 → ℝ → E2 := fun i => F 1 ∘ z i ∘ Theta i
  have hbSmooth (i : Fin 2) : ContDiff ℝ ∞ (beta i) :=
    (F 1).contDiff.comp ((hz i).comp (Theta i).contDiff)
  have hbInj (i : Fin 2) : Injective (beta i) :=
    (F 1).injective.comp ((hzInj i).comp (Theta i).injective)
  have hbReg (i : Fin 2) (t : ℝ) : deriv (beta i) t ≠ 0 := by
    have hzT := deriv.scomp t (hz i |>.differentiable (by simp) (Theta i t))
      ((Theta i).contDiff.differentiable (by simp) t)
    have hzTne : deriv (z i ∘ Theta i) t ≠ 0 := by
      rw [hzT]
      exact smul_ne_zero (((hTheta i).2.2.1 t).ne') (hzReg i (Theta i t))
    have hi : Injective (fderiv ℝ (F 1) (z i (Theta i t))) := by
      have hh := ((F 1).toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
        (x := z i (Theta i t)) (mem_univ _)
      change Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (F 1) (z i (Theta i t))) at hh
      rwa [mfderiv_eq_fderiv] at hh
    rw [show beta i = F 1 ∘ (z i ∘ Theta i) from rfl,
      fderiv_comp_deriv t ((F 1).contDiff.differentiable (by simp) _)
        (((hz i).comp (Theta i).contDiff).differentiable (by simp) t)]
    exact fun h => hzTne (hi (h.trans (map_zero _).symm))
  have hbData (i : Fin 2) : beta i '' Icc (0 : ℝ) 1 = Eta i ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ‖beta i t‖ < 1) ∧
      (∀ t, |t| < nuB → beta i t = (1 - t) • port (ep (i, 1))) ∧
      (∀ t, |t - 1| < nuB → beta i t = t • port (ep (i, 0))) := by
    obtain ⟨_, _, _, _, _, _, h0map, h1map, h0, h1, _, _, h01, h01o, _, _⟩ := hTheta i
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [beta, image_comp, h01, hzImage, Eta]
    · intro t ht
      have ht' : Theta i t ∈ Ioo (0 : ℝ) 1 := h01o ▸ mem_image_of_mem (Theta i) ht
      change ‖F 1 (z i (Theta i t))‖ < 1
      rw [(hFn 1 _).1, hzNorm]; exact hRlt _ ht'
    · intro t ht
      have ht' : t ∈ Icc (-nuB) nuB := by rw [abs_lt] at ht; exact ⟨ht.1.le, ht.2.le⟩
      have hm := h0map ht'
      have he := h0 ht'
      change 1 - R (Theta i t) = t at he
      change F 1 (z i (Theta i t)) = _
      rw [hFLeft i _ (abs_lt.mpr hm), show R (Theta i t) = 1 - t by linarith]
    · intro t ht
      have ht' : t ∈ Icc (1 - nuB) (1 + nuB) := by
        rw [abs_lt] at ht; constructor <;> linarith [ht.1, ht.2]
      have hm := h1map ht'
      have he := h1 ht'
      change R (Theta i t) = t at he
      change F 1 (z i (Theta i t)) = _
      rw [hFRight i _ (abs_lt.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩), he]
  have hEtaSign (i : Fin 2) : Eta i ⊆ {x : E2 | 0 < sign i * (J2 x).2} := by
    rintro y ⟨x, hx, rfl⟩
    have hx2 := hx.2
    have hroot : 0 < Real.sqrt ((J2 x).1 ^ 2 + mu) := Real.sqrt_pos.mpr (by positivity)
    have hh := hFsgn 1 x
    fin_cases i
    · change (J2 x).2 = 1 * _ at hx2
      change 0 < 1 * (J2 (F 1 x)).2
      simpa only [one_mul] using hh.2.2.1.mpr (by linarith [hx2])
    · change (J2 x).2 = -1 * _ at hx2
      change 0 < -1 * (J2 (F 1 x)).2
      have hn : (J2 x).2 < 0 := by linarith [hx2]
      have hn' : ¬ 0 < (J2 (F 1 x)).2 := fun hp => (not_lt_of_ge hn.le) (hh.2.2.1.mp hp)
      have hz' : (J2 (F 1 x)).2 ≠ 0 := fun hz0 => hn.ne (hh.2.2.2.mp hz0)
      nlinarith [lt_of_le_of_ne (le_of_not_gt hn') hz']
  have hAlphaEnds (i : Fin 2) : alpha i 0 = port (ep (i, 0)) ∧ alpha i 1 = port (ep (i, 1)) := by
    constructor
    · simpa using hInitial i 0 (by simpa using hnu)
    · simpa only [show (2 : ℝ) - 1 = 1 by norm_num, one_smul] using
        hTerminal i 1 (by simpa using hnu)
  have hbEnds (i : Fin 2) : beta i 0 = port (ep (i, 1)) ∧ beta i 1 = port (ep (i, 0)) := by
    constructor
    · simpa using (hbData i).2.2.1 0 (by simpa using hnuB)
    · simpa using (hbData i).2.2.2 1 (by simpa using hnuB)
  have hAlphaNorm (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 ≤ ‖alpha i t‖ := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, (hAlphaEnds i).1, hpNorm]
    · rcases eq_or_lt_of_le ht.2 with h' | h'
      · rw [h', (hAlphaEnds i).2, hpNorm]
      · exact (hProper i t ⟨h, h'⟩).le
  let omega : ℝ := min nu (min nuB (1 / 8)) / 4
  have ho : 0 < omega := by dsimp [omega]; positivity
  have hon : omega < nu := by dsimp [omega]; have := min_le_left nu (min nuB (1 / 8)); linarith
  have hob : omega < nuB := by
    have := (min_le_right nu (min nuB (1 / 8))).trans (min_le_left nuB (1 / 8))
    dsimp [omega]; linarith
  have ho8 : omega < 1 / 8 := by
    have := (min_le_right nu (min nuB (1 / 8))).trans (min_le_right nuB (1 / 8))
    dsimp [omega]; linarith
  have htwo : (0 : ℝ) < 2 := by norm_num
  let tau : ℝ → ℝ := toIcoMod htwo 0
  let g : Fin 2 → ℝ → E2 := fun i t => if t ≤ 1 then alpha i t else beta i (t - 1)
  let gamma : Fin 2 → ℝ → E2 := fun i t => g i (tau t)
  have htau (t : ℝ) : tau t ∈ Ico (0 : ℝ) 2 := by simpa [tau] using toIcoMod_mem_Ico htwo 0 t
  have htauSelf {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 2) : tau t = t :=
    (toIcoMod_eq_self htwo).mpr (by simpa using ht)
  have hPer (i : Fin 2) : Periodic (gamma i) 2 := by
    intro t; change g i (toIcoMod htwo 0 (t + 2)) = g i (toIcoMod htwo 0 t)
    rw [toIcoMod_add_right]
  have hGzero (i : Fin 2) {t : ℝ} (ht : |t| < omega) :
      gamma i t = (1 + t) • port (ep (i, 0)) := by
    have hh := abs_lt.mp ht
    by_cases h0 : 0 ≤ t
    · rw [show gamma i t = g i t by
        dsimp [gamma]; rw [htauSelf ⟨h0, by linarith [hh.2]⟩]]
      dsimp only [g]
      rw [if_pos (by linarith [hh.2] : t ≤ 1), hInitial i t (ht.trans hon)]
    · have hm : tau t = t + 2 := (toIcoMod_eq_iff htwo).mpr
        ⟨by constructor <;> linarith [hh.1, hh.2], -1, by norm_num⟩
      dsimp only [gamma]; rw [hm]; dsimp only [g]
      rw [if_neg (by linarith [hh.1] : ¬ t + 2 ≤ 1)]
      rw [(hbData i).2.2.2 (t + 2 - 1) (by
        simpa only [show t + 2 - 1 - 1 = t by ring] using ht.trans hob)]
      congr 1; ring
  have hGone (i : Fin 2) {t : ℝ} (ht : |t - 1| < omega) :
      gamma i t = (2 - t) • port (ep (i, 1)) := by
    have hh := abs_lt.mp ht
    dsimp only [gamma]
    rw [htauSelf ⟨by linarith [hh.1], by linarith [hh.2]⟩]
    dsimp only [g]
    split_ifs with h
    · exact hTerminal i t (ht.trans hon)
    · rw [(hbData i).2.2.1 (t - 1) (ht.trans hob)]
      congr 1; ring
  have hGleft (i : Fin 2) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : gamma i t = alpha i t := by
    dsimp only [gamma]; rw [htauSelf ⟨ht.1.le, by linarith [ht.2]⟩]
    dsimp only [g]; rw [if_pos ht.2.le]
  have hGright (i : Fin 2) {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 2) : gamma i t = beta i (t - 1) := by
    dsimp only [gamma]; rw [htauSelf ⟨by linarith [ht.1], ht.2⟩]
    dsimp only [g]; rw [if_neg (not_le.mpr ht.1)]
  have hGlocal (i : Fin 2) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 2) :
      ContDiffAt ℝ ∞ (gamma i) t ∧ deriv (gamma i) t ≠ 0 := by
    by_cases h0 : t = 0
    · subst t
      have he : gamma i =ᶠ[𝓝 0] fun x => (1 + x) • port (ep (i, 0)) := by
        filter_upwards [Ioo_mem_nhds (by linarith : -omega < 0) ho] with x hx
        exact hGzero i (abs_lt.mpr hx)
      have hs : ContDiff ℝ ∞ (fun x : ℝ => (1 + x) • port (ep (i, 0))) := by fun_prop
      refine ⟨hs.contDiffAt.congr_of_eventuallyEq he, ?_⟩
      have hd : HasDerivAt (fun x : ℝ => (1 + x) • port (ep (i, 0)))
          (port (ep (i, 0))) 0 := by
        simpa using (hasDerivAt_const 0 (1 : ℝ) |>.add (hasDerivAt_id 0)
          |>.smul_const (port (ep (i, 0))))
      rw [he.deriv_eq, hd.deriv]
      exact hpNe (ep (i, 0))
    by_cases h1 : t = 1
    · subst t
      have he : gamma i =ᶠ[𝓝 1] fun x => (2 - x) • port (ep (i, 1)) := by
        filter_upwards [Ioo_mem_nhds (by linarith : 1 - omega < 1)
          (by linarith : 1 < 1 + omega)] with x hx
        exact hGone i (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      have hs : ContDiff ℝ ∞ (fun x : ℝ => (2 - x) • port (ep (i, 1))) := by fun_prop
      refine ⟨hs.contDiffAt.congr_of_eventuallyEq he, ?_⟩
      have hd : HasDerivAt (fun x : ℝ => (2 - x) • port (ep (i, 1)))
          (-port (ep (i, 1))) 1 := by
        simpa using (hasDerivAt_const 1 (2 : ℝ) |>.sub (hasDerivAt_id 1)
          |>.smul_const (port (ep (i, 1))))
      rw [he.deriv_eq, hd.deriv]
      exact neg_ne_zero.mpr (hpNe (ep (i, 1)))
    by_cases hlt : t < 1
    · have hI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), hlt⟩
      have hOld : t ∈ Ioo (-nu) (1 + nu) := ⟨by linarith [hI.1], by linarith [hI.2]⟩
      have he : gamma i =ᶠ[𝓝 t] alpha i := by
        filter_upwards [isOpen_Ioo.mem_nhds hI] with x hx; exact hGleft i hx
      refine ⟨((hAlpha i).contDiffAt (isOpen_Ioo.mem_nhds hOld)).congr_of_eventuallyEq he, ?_⟩
      rw [he.deriv_eq]; exact hAlphaReg i t hOld
    · have hI : t ∈ Ioo (1 : ℝ) 2 := ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h1), ht.2⟩
      have he : gamma i =ᶠ[𝓝 t] fun x => beta i (x - 1) := by
        filter_upwards [isOpen_Ioo.mem_nhds hI] with x hx; exact hGright i hx
      have hd : HasDerivAt (fun x => beta i (x - 1)) (deriv (beta i) (t - 1)) t := by
        simpa only [Function.comp_def, id_eq, one_smul] using
          ((hbSmooth i).differentiable (by simp) (t - 1)).hasDerivAt.scomp t
            ((hasDerivAt_id t).sub_const 1)
      have hs : ContDiff ℝ ∞ (fun x : ℝ => beta i (x - 1)) :=
        (hbSmooth i).comp (contDiff_id.sub contDiff_const)
      refine ⟨hs.contDiffAt.congr_of_eventuallyEq he, ?_⟩
      rw [he.deriv_eq, hd.deriv]; exact hbReg i (t - 1)
  have hGall (i : Fin 2) (t : ℝ) : ContDiffAt ℝ ∞ (gamma i) t ∧ deriv (gamma i) t ≠ 0 := by
    let k : ℤ := toIcoDiv htwo 0 t
    let d : ℝ := k • (2 : ℝ)
    have hr : t - d = tau t := rfl
    have he : (fun x => gamma i (x - d)) = gamma i := funext fun x => (hPer i).sub_zsmul_eq k
    have hc := (hGlocal i (tau t) (htau t)).1
    have hc' : ContDiffAt ℝ ∞ (gamma i) (t - d) := by simpa only [hr] using hc
    have hd := (hc'.differentiableAt (by simp)).hasDerivAt.scomp t ((hasDerivAt_id t).sub_const d)
    have hcs : ContDiffAt ℝ ∞ (fun x => gamma i (x - d)) t := by
      have hsub : ContDiffAt ℝ ∞ (fun x : ℝ => x - d) t :=
        contDiffAt_id.sub contDiffAt_const
      simpa only [Function.comp_def] using hc'.comp t hsub
    refine ⟨he ▸ hcs, ?_⟩
    have hd' : deriv (fun x => gamma i (x - d)) t = deriv (gamma i) (tau t) := by
      simpa only [Function.comp_def, id_eq, hr, one_smul] using hd.deriv
    rw [he] at hd'; rw [hd']; exact (hGlocal i (tau t) (htau t)).2
  have hGinj (i : Fin 2) : InjOn (g i) (Ico (0 : ℝ) 2) := by
    intro t ht u hu h
    by_cases ht1 : t ≤ 1 <;> by_cases hu1 : u ≤ 1
    · simp only [g, if_pos ht1, if_pos hu1] at h
      exact hAlphaInj i ⟨by linarith [ht.1], by linarith⟩ ⟨by linarith [hu.1], by linarith⟩ h
    · simp only [g, if_pos ht1, if_neg hu1] at h
      have ha := hAlphaNorm i t ⟨ht.1, ht1⟩
      have hb := (hbData i).2.1 (u - 1) ⟨by linarith, by linarith [hu.2]⟩
      rw [h] at ha; linarith
    · simp only [g, if_neg ht1, if_pos hu1] at h
      have ha := hAlphaNorm i u ⟨hu.1, hu1⟩
      have hb := (hbData i).2.1 (t - 1) ⟨by linarith, by linarith [ht.2]⟩
      rw [← h] at ha; linarith
    · simp only [g, if_neg ht1, if_neg hu1] at h
      have hh := hbInj i h
      linarith
  have hGimage (i : Fin 2) : g i '' Ico (0 : ℝ) 2 =
      (alpha i '' Icc (0 : ℝ) 1) ∪ (beta i '' Icc (0 : ℝ) 1) := by
    ext y; constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases h : t ≤ 1
      · exact Or.inl ⟨t, ⟨ht.1, h⟩, by simp [g, h]⟩
      · exact Or.inr ⟨t - 1, ⟨by linarith, by linarith [ht.2]⟩, by simp [g, h]⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, by simp [g, ht.2]⟩
      · by_cases h0 : t = 0
        · subst t; exact ⟨1, by norm_num, by simp [g, (hAlphaEnds i).2, (hbEnds i).1]⟩
        by_cases h1 : t = 1
        · subst t; exact ⟨0, by norm_num, by simp [g, (hAlphaEnds i).1, (hbEnds i).2]⟩
        have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
        refine ⟨t + 1, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
        simp [g, show ¬ t + 1 ≤ 1 by have := lt_of_le_of_ne ht.1 (Ne.symm h0); linarith]
  let H := periodUnitCircleHomeomorph 2 (by norm_num)
  let E := QuotientAddGroup.equivIcoMod htwo (0 : ℝ)
  let c : Fin 2 → UnitCircle → E2 := fun i q => g i (E (H.symm q))
  have hcLift (i : Fin 2) : c i ∘ periodCircleParam 2 = gamma i := by
    funext t
    change g i (E (H.symm (periodCircleParam 2 t))) = g i (tau t)
    rw [← periodUnitCircleHomeomorph_coe 2 (by norm_num) t]
    change g i (E (H.symm (H (t : AddCircle (2 : ℝ))))) = _
    rw [H.symm_apply_apply]; rfl
  have hcInj (i : Fin 2) : Injective (c i) := by
    intro p q hpq
    apply H.symm.injective
    apply E.injective
    apply Subtype.ext
    exact hGinj i (by simpa using (E (H.symm p)).property)
      (by simpa using (E (H.symm q)).property) hpq
  have hc (i : Fin 2) : IsPlanarEmbedding (c i) := by
    have hsmooth : ContDiff ℝ ∞ (c i ∘ periodCircleParam 2) := by
      rw [hcLift]; exact contDiff_iff_contDiffAt.mpr (fun t => (hGall i t).1)
    have hregular : ∀ t, deriv (c i ∘ periodCircleParam 2) t ≠ 0 := by
      rw [hcLift]; exact fun t => (hGall i t).2
    exact ⟨contMDiff_of_smooth_period_lift 2 (by norm_num) (c i) hsmooth, hcInj i,
      mfderiv_injective_of_nonzero_period_lift 2 (by norm_num) (c i) hsmooth hregular⟩
  have hcImage (i : Fin 2) : range (c i) = (alpha i '' Icc (0 : ℝ) 1) ∪ Eta i := by
    have he : range (c i) = g i '' Ico (0 : ℝ) 2 := by
      ext y; constructor
      · rintro ⟨q, rfl⟩; exact ⟨E (H.symm q), by simpa using (E (H.symm q)).property, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨H (E.symm ⟨t, by simpa using ht⟩), by simp [c]⟩
    rw [he, hGimage, (hbData i).1]
  let D : (i : Fin 2) → PlanarSchoenfliesData (c i) := fun i => Classical.choice (hP.1 (c i) (hc i))
  let B : Fin 2 → BallNeighborhoodChart E2 E2 := fun i => (D i).ballNeighborhoodChart
  have hBoundary (i : Fin 2) : (B i).boundary = range (c i) := (D i).discChart_image_sphere
  have hBoundarySign (i : Fin 2) : (B i).boundary ⊆ {x : E2 | 0 < sign i * (J2 x).2} := by
    rw [hBoundary, hcImage]
    rintro x (⟨t, ht, rfl⟩ | hx)
    · exact hSign i t ht
    · exact hEtaSign i hx
  have hFilled (i : Fin 2) : (B i).closedRegion ⊆ {x : E2 | 0 < sign i * (J2 x).2} := by
    let ell : E2 → ℝ := fun x => sign i * (J2 x).2
    have hell : Continuous ell := continuous_const.mul (continuous_snd.comp J2.continuous)
    have hne : (B i).closedRegion.Nonempty := ⟨(B i).chart 0, 0, by simp, rfl⟩
    obtain ⟨x0, hx0, hmin⟩ := (B i).closedRegion_compact.exists_isMinOn hne hell.continuousOn
    have hnot : x0 ∉ (B i).inside := by
      intro hx
      obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp (B i).inside_open x0 hx
      let w : E2 := J2.symm (0, -sign i)
      have hw : ‖w‖ = 1 := by
        have hh := hn 0 (-sign i)
        change ‖w‖ ^ 2 = _ at hh
        rw [zero_pow (by norm_num), neg_sq, (hsig i).1, zero_add] at hh
        nlinarith [norm_nonneg w]
      let y : E2 := x0 + (eps / 2) • w
      have hyIn : y ∈ (B i).inside := hball (by
        change dist (x0 + (eps / 2) • w) x0 < eps
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hw, mul_one, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < eps / 2)]
        linarith)
      have hyC : y ∈ (B i).closedRegion := image_mono ball_subset_closedBall hyIn
      have he : ell y = ell x0 - eps / 2 := by
        dsimp [ell, y, w]
        simp only [map_add, map_smul, J2.apply_symm_apply, Prod.smul_mk,
          smul_eq_mul]
        change sign i * ((J2 x0).2 + eps / 2 * -sign i) = sign i * (J2 x0).2 - eps / 2
        nlinarith [congrArg (fun q : ℝ => eps / 2 * q) (hsig i).1]
      have hle : ell x0 ≤ ell y := hmin hyC
      rw [he] at hle; linarith
    have hb : x0 ∈ (B i).boundary := by
      rw [← (B i).inside_union_boundary] at hx0
      exact hx0.resolve_left hnot
    have hp : 0 < ell x0 := hBoundarySign i hb
    intro y hy
    exact hp.trans_le (hmin hy)
  refine ⟨c, B, hc, hcImage, hBoundary, hFilled, Set.disjoint_left.mpr ?_⟩
  intro x hx0 hx1
  have h0 := hFilled 0 hx0
  have h1 := hFilled 1 hx1
  change 0 < 1 * (J2 x).2 at h0
  change 0 < -1 * (J2 x).2 at h1
  linarith

end PoincareConjecture.M25.Topology3D
