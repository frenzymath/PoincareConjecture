import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceCapMeridian
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactSmoothChart
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_outer_cap_projection_chart
    (F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hF : ContDiff ℝ ∞ (fun z : E2 × ℝ => F z.2 z.1))
    (hfix : ∀ (a : ℝ) (x : E2), ‖x‖ ≤ 1 / 8 → F a x = x)
    (hray : ∀ e : E2, ‖e‖ = 1 → ∃ p : ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ p ∧ (∀ a : ℝ, p (a, 0) = 0) ∧
      (∀ a r : ℝ, 0 < r → F a (r • e) = p (a, r) • e) ∧
      (∀ a r : ℝ, 0 < deriv (fun s : ℝ => p (a, s)) r) ∧
      (∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
        ∀ r : ℝ, 0 < r → deriv (fun s : ℝ => p (s, r)) a ≤ 0) ∧
      ∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
        deriv (fun s : ℝ => p (s, 1)) a < 0)
    (h lambda : ℝ) (hh : |h - 17 / 16| ≤ 1 / 32768)
    (hlambda : 0 < lambda) (hsmall : lambda < 1 / 131072) :
    let a := stackCanonicalHorizontal (1 / 4) (1 / 2)
    let b := stackCanonicalVertical (1 / 4) (1 / 2)
    let M := stackCapProfilePath a a b b 0
    let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
    let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
    let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
    let f : E2 → E2 := fun x => F (h - lambda * (C x).2) (C x).1
    ContDiff ℝ ∞ f ∧
      (∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ ball (0 : E2) eps,
        f x = (2 / (1 + ‖x‖ ^ 2)) • x) ∧
      (∀ x : E2, |v x| < 1 / 4 → (C x).2 = v x ∧ ‖(C x).1‖ = 1) ∧
      (∀ x ∈ sphere (0 : E2) 1, f x = F h x) ∧
      f '' closedBall (0 : E2) 1 = F h '' closedBall (0 : E2) 1 ∧
      ∃ e : OpenPartialHomeomorph E2 E2,
        (e : E2 → E2) = f ∧ closedBall (0 : E2) 1 ⊆ e.source ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let a := stackCanonicalHorizontal (1 / 4) (1 / 2)
  let b := stackCanonicalVertical (1 / 4) (1 / 2)
  let M := stackCapProfilePath a a b b 0
  let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
  let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
  let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
  let f : E2 → E2 := fun x => F (h - lambda * (C x).2) (C x).1
  let R : ℝ → ℝ := fun t =>
    (stackCanonicalMeridian (1 / 4) (1 / 2) (1 / 4) (1 / 2) t).1
  let Z : ℝ → ℝ := fun t =>
    (stackCanonicalMeridian (1 / 4) (1 / 2) (1 / 4) (1 / 2) t).2
  let nu : ℝ → ℝ := fun r => (r ^ 2 - 1) / (1 + r ^ 2)
  obtain ⟨_, hCs, _, _, _, hcoords, _, hcanonical, _, _, _, _⟩ :=
    stackMorseProjection_geometry (1 / 4) (1 / 2) (1 / 4) (1 / 2) 1 (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change ContDiff ℝ ∞ C at hCs
  obtain ⟨_, hapos, _, _, hanear, hafar, _⟩ :=
    stackCanonicalHorizontal_spec (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, _, _, _, hbfar, _⟩ :=
    stackCanonicalVertical_spec (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  have hD (x : E2) : 0 < 1 + ‖x‖ ^ 2 := by positivity
  let k : E2 → ℝ := fun x => a (v x) * (2 / (1 + ‖x‖ ^ 2))
  have hk (x : E2) : 0 < k x := mul_pos (hapos _)
    (div_pos (by norm_num) (hD x))
  have hC1 (x : E2) : (C x).1 = k x • x := (hcoords x).2.2.2.1
  have hC2 (x : E2) : (C x).2 = Z (v x) := (hcoords x).2.2.2.2.1
  have hCn (x : E2) : ‖(C x).1‖ = R (v x) := (hcoords x).2.2.2.2.2.1
  have hkn (x : E2) : k x * ‖x‖ = R (v x) := by
    have hn := hCn x
    rwa [hC1, norm_smul, Real.norm_eq_abs, abs_of_pos (hk x)] at hn
  have hmem (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      v x ∈ Icc (-1 : ℝ) 0 := (hcanonical x hx).1
  have hnorm (e : E2) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 ≤ r) : ‖r • e‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, he, mul_one]
  have hvray (e : E2) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 ≤ r) : v (r • e) = nu r := by
    dsimp only [v, nu]
    rw [hnorm e he r hr]
  have hC1ray (e : E2) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
      (C (r • e)).1 = R (nu r) • e := by
    rw [hC1, smul_smul]
    congr 1
    calc
      k (r • e) * r = k (r • e) * ‖r • e‖ := by rw [hnorm e he r hr]
      _ = R (nu r) := by rw [hkn, hvray e he r hr]
  have hRray (e : E2) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) : 0 < R (nu r) := by
    rw [← hvray e he r hr.le, ← hkn, hnorm e he r hr.le]
    exact mul_pos (hk _) hr
  have hfray (e : E2) (he : ‖e‖ = 1) (p : ℝ × ℝ → ℝ)
      (hpray : ∀ a r : ℝ, 0 < r → F a (r • e) = p (a, r) • e)
      (r : ℝ) (hr : 0 < r) :
      f (r • e) = p (h - lambda * Z (nu r), R (nu r)) • e := by
    change F (h - lambda * (C (r • e)).2) (C (r • e)).1 = _
    rw [hC2, hvray e he r hr.le, hC1ray e he r hr.le]
    exact hpray _ _ (hRray e he r hr)
  have hnormal (x : E2) (hx : x ≠ 0) :
      ‖‖x‖⁻¹ • x‖ = 1 ∧ ‖x‖ • (‖x‖⁻¹ • x) = x := by
    have hn := norm_pos_iff.mpr hx
    constructor
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    · rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hFzero (a : ℝ) : F a 0 = 0 := hfix a 0 (by norm_num)
  have hfzero : f 0 = 0 := by
    change F (h - lambda * (C 0).2) (C 0).1 = 0
    rw [hC1, smul_zero, hFzero]
  have hfs : ContDiff ℝ ∞ f := hF.comp
    (hCs.fst.prodMk (contDiff_const.sub (contDiff_const.mul hCs.snd)))
  have hpositive (x : E2) (hx : x ≠ 0) : ∃ t : ℝ, 0 < t ∧ f x = t • x := by
    let e : E2 := ‖x‖⁻¹ • x
    obtain ⟨he, hxe⟩ := hnormal x hx
    change ‖e‖ = 1 at he
    change ‖x‖ • e = x at hxe
    obtain ⟨p, _hp, hpzero, hpray, hpr, _hph, _hphOne⟩ := hray e he
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let w := p (h - lambda * Z (nu ‖x‖), R (nu ‖x‖))
    have hw : 0 < w := by
      have hm := strictMono_of_deriv_pos (hpr (h - lambda * Z (nu ‖x‖)))
      simpa only [hpzero] using hm (hRray e he ‖x‖ hr)
    have hf : f x = w • e := by simpa only [hxe] using hfray e he p hpray ‖x‖ hr
    refine ⟨w * ‖x‖⁻¹, mul_pos hw (inv_pos.mpr hr), ?_⟩
    rw [hf]
    exact smul_smul w ‖x‖⁻¹ x
  let alpha : E2 → ℝ := fun x => ‖f x‖ / ‖x‖
  have halpha (x : E2) (hx : x ≠ 0) : 0 < alpha x ∧ f x = alpha x • x := by
    obtain ⟨t, ht, hf⟩ := hpositive x hx
    have he : alpha x = t := by
      dsimp only [alpha]
      rw [hf, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hx)]
    exact ⟨he ▸ ht, he ▸ hf⟩
  have hfne (x : E2) (hx : x ≠ 0) : f x ≠ 0 := by
    rw [(halpha x hx).2]
    exact smul_ne_zero (halpha x hx).1.ne' hx
  have hnormalized (x : E2) (hx : x ≠ 0) :
      ‖f x‖⁻¹ • f x = ‖x‖⁻¹ • x := by
    rw [(halpha x hx).2, norm_smul, Real.norm_eq_abs,
      abs_of_pos (halpha x hx).1, smul_smul]
    congr 1
    field_simp [(halpha x hx).1.ne', norm_ne_zero_iff.mpr hx]
  have hnuInj (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (he : nu r = nu s) : r = s := by
    have hd1 : 1 + r ^ 2 ≠ 0 := by positivity
    have hd2 : 1 + s ^ 2 ≠ 0 := by positivity
    have hh := (div_eq_div_iff hd1 hd2).mp he
    nlinarith only [hh, hr, hs]
  have hinj : InjOn f (closedBall (0 : E2) 1) := by
    intro x hx y hy hxy
    by_cases hx0 : x = 0
    · subst x
      by_contra hy0
      exact hfne y (Ne.symm hy0) (hxy.symm.trans hfzero)
    by_cases hy0 : y = 0
    · subst y
      exact False.elim (hfne x hx0 (hxy.trans hfzero))
    let e : E2 := ‖x‖⁻¹ • x
    obtain ⟨he, hxe⟩ := hnormal x hx0
    change ‖e‖ = 1 at he
    change ‖x‖ • e = x at hxe
    have heq : e = ‖y‖⁻¹ • y := by
      change ‖x‖⁻¹ • x = ‖y‖⁻¹ • y
      rw [← hnormalized x hx0, ← hnormalized y hy0, hxy]
    have hye : ‖y‖ • e = y := by rw [heq]; exact (hnormal y hy0).2
    obtain ⟨p, hp, hpzero, hpray, hpr, hph, hphOne⟩ := hray e he
    let W : ℝ → ℝ := fun t => p (h - lambda * Z t, R t)
    obtain ⟨_, hWpole, _, _, _, _, hm, _⟩ := outer_cap_meridian_geometry
      p hp hpzero hpr hph hphOne h lambda hh hlambda hsmall
    change W (-1) = 0 at hWpole
    change StrictMonoOn W (Icc (-1 : ℝ) 0) at hm
    have hxv : nu ‖x‖ ∈ Icc (-1 : ℝ) 0 := hmem x hx
    have hyv : nu ‖y‖ ∈ Icc (-1 : ℝ) 0 := hmem y hy
    have hWx : 0 ≤ W (nu ‖x‖) := by
      simpa only [hWpole] using hm.monotoneOn (by simp) hxv hxv.1
    have hWy : 0 ≤ W (nu ‖y‖) := by
      simpa only [hWpole] using hm.monotoneOn (by simp) hyv hyv.1
    have hfx : f x = W (nu ‖x‖) • e := by
      simpa only [hxe] using hfray e he p hpray ‖x‖ (norm_pos_iff.mpr hx0)
    have hfy : f y = W (nu ‖y‖) • e := by
      simpa only [hye] using hfray e he p hpray ‖y‖ (norm_pos_iff.mpr hy0)
    have hn := congrArg norm hxy
    rw [hfx, hfy] at hn
    simp only [norm_smul, Real.norm_eq_abs, he,
      abs_of_nonneg hWx, abs_of_nonneg hWy, mul_one] at hn
    have hnxy := hnuInj ‖x‖ ‖y‖ (norm_nonneg _) (norm_nonneg _) (hm.injOn hxv hyv hn)
    calc
      x = ‖x‖ • e := hxe.symm
      _ = ‖y‖ • e := by rw [hnxy]
      _ = y := hye
  have hnuPre (t : ℝ) (ht : t ∈ Ioc (-1 : ℝ) 0) :
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ nu r = t := by
    have hd : 0 < 1 - t := by linarith only [ht.2]
    have hn : 0 < 1 + t := by linarith only [ht.1]
    let r := Real.sqrt ((1 + t) / (1 - t))
    have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hn hd)
    have hr2 : r ^ 2 = (1 + t) / (1 - t) := Real.sq_sqrt (div_pos hn hd).le
    have heq : r ^ 2 * (1 - t) = 1 + t := (eq_div_iff hd.ne').mp hr2
    have hrle : r ≤ 1 := by
      have hs : r ^ 2 ≤ 1 := by
        rw [hr2]
        exact (div_le_one hd).mpr (by linarith only [ht.2])
      nlinarith only [hs, hr]
    refine ⟨r, hr, hrle, ?_⟩
    apply (div_eq_iff (show 1 + r ^ 2 ≠ 0 by positivity)).mpr
    nlinarith only [heq]
  have himage : f '' closedBall (0 : E2) 1 = F h '' closedBall (0 : E2) 1 := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      by_cases hx0 : x = 0
      · subst x
        exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), (hFzero h).trans hfzero.symm⟩
      let e : E2 := ‖x‖⁻¹ • x
      obtain ⟨he, hxe⟩ := hnormal x hx0
      change ‖e‖ = 1 at he
      change ‖x‖ • e = x at hxe
      obtain ⟨p, hp, hpzero, hpray, hpr, hph, hphOne⟩ := hray e he
      let W : ℝ → ℝ := fun t => p (h - lambda * Z t, R t)
      obtain ⟨_, hWpole, hWzero, _, _, _, hm, _⟩ := outer_cap_meridian_geometry
        p hp hpzero hpr hph hphOne h lambda hh hlambda hsmall
      change W (-1) = 0 at hWpole
      change W 0 = p (h, 1) at hWzero
      change StrictMonoOn W (Icc (-1 : ℝ) 0) at hm
      have hvx : nu ‖x‖ ∈ Icc (-1 : ℝ) 0 := hmem x hx
      have hWlo : 0 ≤ W (nu ‖x‖) := by
        simpa only [hWpole] using hm.monotoneOn (by simp) hvx hvx.1
      have hWhi : W (nu ‖x‖) ≤ p (h, 1) := by
        simpa only [hWzero] using hm.monotoneOn hvx (by simp) hvx.2
      have hg : Continuous (fun r : ℝ => p (h, r)) :=
        hp.continuous.comp (continuous_const.prodMk continuous_id)
      have hgi : (fun r : ℝ => p (h, r)) '' Icc 0 1 = Icc 0 (p (h, 1)) := by
        simpa only [hpzero] using ContinuousOn.image_Icc_of_monotoneOn
          (by norm_num : (0 : ℝ) ≤ 1) hg.continuousOn
          ((strictMono_of_deriv_pos (hpr h)).monotone.monotoneOn _)
      obtain ⟨r, hr, hreq⟩ := hgi.symm ▸ (show W (nu ‖x‖) ∈ Icc 0 (p (h, 1)) from ⟨hWlo, hWhi⟩)
      change p (h, r) = W (nu ‖x‖) at hreq
      refine ⟨r • e, mem_closedBall_zero_iff.mpr ((hnorm e he r hr.1).le.trans hr.2), ?_⟩
      have hfx : f x = W (nu ‖x‖) • e := by
        simpa only [hxe] using hfray e he p hpray ‖x‖ (norm_pos_iff.mpr hx0)
      by_cases hr0 : r = 0
      · subst r
        rw [zero_smul, hFzero, hfx, ← hreq, hpzero, zero_smul]
      · rw [hpray h r (lt_of_le_of_ne hr.1 (Ne.symm hr0)), hreq, hfx]
    · rintro y ⟨x, hx, rfl⟩
      by_cases hx0 : x = 0
      · subst x
        exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), hfzero.trans (hFzero h).symm⟩
      let e : E2 := ‖x‖⁻¹ • x
      obtain ⟨he, hxe⟩ := hnormal x hx0
      change ‖e‖ = 1 at he
      change ‖x‖ • e = x at hxe
      obtain ⟨p, hp, hpzero, hpray, hpr, hph, hphOne⟩ := hray e he
      let W : ℝ → ℝ := fun t => p (h - lambda * Z t, R t)
      obtain ⟨_, hWpole, _, _, _, _, _, hWi⟩ := outer_cap_meridian_geometry
        p hp hpzero hpr hph hphOne h lambda hh hlambda hsmall
      change W (-1) = 0 at hWpole
      change W '' Icc (-1 : ℝ) 0 = Icc 0 (p (h, 1)) at hWi
      have hpm := strictMono_of_deriv_pos (hpr h)
      have hpPos : 0 < p (h, ‖x‖) := by
        simpa only [hpzero] using hpm (norm_pos_iff.mpr hx0)
      have hpLe : p (h, ‖x‖) ≤ p (h, 1) := hpm.monotone (mem_closedBall_zero_iff.mp hx)
      obtain ⟨t, ht, hwt⟩ := hWi.symm ▸ (show p (h, ‖x‖) ∈ Icc 0 (p (h, 1)) from ⟨hpPos.le, hpLe⟩)
      have htlo : -1 < t := by
        apply lt_of_le_of_ne ht.1
        intro hteq
        rw [← hteq, hWpole] at hwt
        exact hpPos.ne' hwt.symm
      obtain ⟨r, hr, hrle, hrt⟩ := hnuPre t ⟨htlo, ht.2⟩
      refine ⟨r • e, mem_closedBall_zero_iff.mpr ((hnorm e he r hr.le).le.trans hrle), ?_⟩
      have hFx : F h x = p (h, ‖x‖) • e := by
        simpa only [hxe] using hpray h ‖x‖ (norm_pos_iff.mpr hx0)
      rw [hfray e he p hpray r hr]
      change W (nu r) • e = F h x
      rw [hrt, hwt, hFx]
  have hvc : Continuous v :=
    ((continuous_norm.pow 2).sub continuous_const).div
      (continuous_const.add (continuous_norm.pow 2)) (fun x => (hD x).ne')
  have hvzero : v 0 = -1 := by simp only [v, norm_zero]; norm_num
  have hCzero : (C 0).1 = 0 := by rw [hC1, smul_zero]
  have hopen : IsOpen {x : E2 | v x < -1 / 2 ∧ ‖(C x).1‖ < 1 / 8} :=
    (isOpen_lt hvc continuous_const).inter (isOpen_lt hCs.fst.continuous.norm continuous_const)
  have h0mem : (0 : E2) ∈ {x : E2 | v x < -1 / 2 ∧ ‖(C x).1‖ < 1 / 8} := by
    change v 0 < -1 / 2 ∧ ‖(C 0).1‖ < 1 / 8
    rw [hvzero, hCzero, norm_zero]
    norm_num
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0mem
  have hpole (x : E2) (hx : x ∈ ball (0 : E2) eps) :
      f x = (2 / (1 + ‖x‖ ^ 2)) • x := by
    have hxv := (hball hx).1
    have ha : a (v x) = 1 := hafar _ (by
      rw [abs_of_neg (by linarith : v x < 0)]
      linarith only [hxv])
    change F (h - lambda * (C x).2) (C x).1 = _
    rw [hfix _ _ (hball hx).2.le, hC1]
    dsimp only [k]
    rw [ha, one_mul]
  have hseam (x : E2) (hx : |v x| < 1 / 4) :
      (C x).2 = v x ∧ ‖(C x).1‖ = 1 := by
    have hvabs : |v x| < 1 := hx.trans (by norm_num)
    have hv2 : v x ^ 2 < 1 := by
      simpa only [sq_abs, one_pow] using
        (sq_lt_sq₀ (abs_nonneg (v x)) zero_le_one).mpr hvabs
    have hs : 0 < Real.sqrt (1 - v x ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hv2)
    have hcn : ‖(C x).1‖ = 1 := by
      rw [hCn]
      change a (v x) * Real.sqrt (1 - v x ^ 2) = 1
      have ha : a (v x) = (Real.sqrt (1 - v x ^ 2))⁻¹ := hanear _ hx.le
      rw [ha, inv_mul_cancel₀ hs.ne']
    refine ⟨?_, hcn⟩
    have hcf : (C x).2 = b (C x).1 * v x := by
      rw [hC2]
      change stackCanonicalFactor ((1 / 4 : ℝ) ^ 2) ((1 / 2 : ℝ) ^ 2)
        (R (v x) ^ 2) * v x = _
      rw [← hCn]
      rfl
    have hb : b (C x).1 = 1 := hbfar _ (by rw [hcn]; norm_num)
    rw [hcf, hb, one_mul]
  have hboundary (x : E2) (hx : x ∈ sphere (0 : E2) 1) : f x = F h x := by
    have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hvx : v x = 0 := by dsimp only [v]; rw [hxn]; norm_num
    have ha0 : a 0 = 1 := by
      have ht := hanear 0 (by norm_num : |(0 : ℝ)| ≤ 1 / 4)
      simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_one, inv_one] using ht
    have hcx : (C x).1 = x := by rw [hC1]; dsimp only [k]; rw [hvx, ha0, hxn]; norm_num
    have hcz : (C x).2 = 0 := by
      rw [hC2, hvx]
      simp only [Z, stackCanonicalMeridian, mul_zero]
    change F (h - lambda * (C x).2) (C x).1 = F h x
    rw [hcx, hcz, mul_zero, sub_zero]
  have hequiv (L : E2 →L[ℝ] E2) (hi : Function.Injective L) :
      ∃ A : E2 ≃L[ℝ] E2, (A : E2 →L[ℝ] E2) = L := by
    let A := (LinearEquiv.ofBijective L.toLinearMap
      ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
    exact ⟨A, by ext z; rfl⟩
  have hregular (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      ∃ A : E2 ≃L[ℝ] E2, HasFDerivAt f (A : E2 →L[ℝ] E2) x := by
    by_cases hx0 : x = 0
    · subst x
      let c : E2 → ℝ := fun y => 2 / (1 + ‖y‖ ^ 2)
      have hcs : ContDiff ℝ ∞ c :=
        contDiff_const.div (contDiff_const.add (contDiff_id.norm_sq ℝ))
          (fun y => (hD y).ne')
      have hd : HasFDerivAt (fun y : E2 => c y • y)
          (c 0 • ContinuousLinearMap.id ℝ E2 + (fderiv ℝ c 0).smulRight (0 : E2)) 0 :=
        (hcs.differentiable (by simp) 0).hasFDerivAt.fun_smul (hasFDerivAt_id (0 : E2))
      have hd0 : HasFDerivAt f ((2 : ℝ) • ContinuousLinearMap.id ℝ E2) 0 := by
        have hd' : HasFDerivAt (fun y : E2 => c y • y)
            ((2 : ℝ) • ContinuousLinearMap.id ℝ E2) 0 := by
          simpa only [c, id_eq, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero,
            div_one, ContinuousLinearMap.smulRight_zero, add_zero] using hd
        apply hd'.congr_of_eventuallyEq
        filter_upwards [Metric.ball_mem_nhds (0 : E2) heps] with y hy
        exact hpole y hy
      obtain ⟨A, hA⟩ := hequiv ((2 : ℝ) • ContinuousLinearMap.id ℝ E2) (by
        intro y z he
        change (2 : ℝ) • y = (2 : ℝ) • z at he
        exact (smul_right_injective E2 (by norm_num : (2 : ℝ) ≠ 0)) he)
      exact ⟨A, hA ▸ hd0⟩
    let r := ‖x‖
    let e : E2 := r⁻¹ • x
    have hr : 0 < r := norm_pos_iff.mpr hx0
    obtain ⟨he, hxe⟩ := hnormal x hx0
    change ‖e‖ = 1 at he
    change r • e = x at hxe
    obtain ⟨p, hp, hpzero, hpray, hpr, hph, hphOne⟩ := hray e he
    let W : ℝ → ℝ := fun t => p (h - lambda * Z t, R t)
    obtain ⟨_, _, _, _, _, hWd, _, _⟩ := outer_cap_meridian_geometry
      p hp hpzero hpr hph hphOne h lambda hh hlambda hsmall
    have ht : nu r ∈ Ioc (-1 : ℝ) 0 := by
      refine ⟨?_, (hmem x hx).2⟩
      apply (lt_div_iff₀ (show 0 < 1 + r ^ 2 by positivity)).mpr
      nlinarith only [sq_pos_of_pos hr]
    have hwd : HasDerivAt W (deriv W (nu r)) (nu r) :=
      (hWd (nu r) ht).1.differentiableAt.hasDerivAt
    let d := deriv W (nu r) * (4 * r / (1 + r ^ 2) ^ 2)
    have hdpos : 0 < d := mul_pos (hWd (nu r) ht).2
      (div_pos (mul_pos (by norm_num) hr) (sq_pos_of_pos (by positivity)))
    have hnud : HasDerivAt nu (4 * r / (1 + r ^ 2) ^ 2) r := by
      have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
        simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using hasDerivAt_pow 2 r
      exact ((hpow.sub_const 1).div (hpow.const_add 1) (by positivity)).congr_deriv (by ring)
    have hrad : HasDerivAt (fun t : ℝ => f (t • e)) (d • e) r := by
      apply ((hwd.comp r hnud).smul_const e).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
      exact hfray e he p hpray t ht
    let L := fderiv ℝ f x
    have hLf : HasFDerivAt f L x := (hfs.differentiable (by simp) x).hasFDerivAt
    have hLe : L e = d • e := by
      have hh : HasFDerivAt f L (r • e) := hxe.symm ▸ hLf
      have hc := hh.comp_hasDerivAt r ((hasDerivAt_id r).smul_const e)
      simpa only [one_smul, Function.comp_def, id_eq] using hc.unique hrad
    have hLx : L x = d • x := by
      calc
        L x = L (r • e) := congrArg L hxe.symm
        _ = r • (d • e) := by rw [map_smul, hLe]
        _ = d • x := by rw [smul_comm, hxe]
    have haSmooth : ContDiffAt ℝ ∞ alpha x :=
      (hfs.contDiffAt.norm ℝ (hfne x hx0)).div (contDiffAt_norm ℝ hx0)
        (norm_ne_zero_iff.mpr hx0)
    let B := fderiv ℝ alpha x
    have hB : HasFDerivAt alpha B x := (haSmooth.differentiableAt (by simp)).hasFDerivAt
    have hformula : L = alpha x • ContinuousLinearMap.id ℝ E2 + B.smulRight x := by
      have hd := hB.fun_smul (hasFDerivAt_id x)
      have hd' : HasFDerivAt f
          (alpha x • ContinuousLinearMap.id ℝ E2 + B.smulRight x) x := by
        apply hd.congr_of_eventuallyEq
        filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
        exact (halpha y hy).2
      exact hLf.unique hd'
    have hker (z : E2) (hz : L z = 0) : z = 0 := by
      have hz' : alpha x • z + B z • x = 0 := by
        simpa only [hformula, add_apply, smul_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply] using hz
      let t := -(alpha x)⁻¹ * B z
      have hzt : z = t • x := by
        have heq : alpha x • z = -(B z • x) := eq_neg_of_add_eq_zero_left hz'
        have hi := congrArg (fun y : E2 => (alpha x)⁻¹ • y) heq
        simpa only [smul_smul, inv_mul_cancel₀ (halpha x hx0).1.ne', one_smul,
          smul_neg, ← neg_smul, neg_mul, mul_neg, t] using hi
      have ht0 : t = 0 := by
        have hz'' : t • (d • x) = 0 := by
          calc
            t • (d • x) = L (t • x) := by rw [map_smul, hLx]
            _ = L z := congrArg L hzt.symm
            _ = 0 := hz
        exact (smul_eq_zero.mp hz'').resolve_right (smul_ne_zero hdpos.ne' hx0)
      rw [hzt, ht0, zero_smul]
    obtain ⟨A, hA⟩ := hequiv L (by
      intro y z hyz
      apply sub_eq_zero.mp
      apply hker
      rw [map_sub, hyz, sub_self])
    exact ⟨A, hA ▸ hLf⟩
  obtain ⟨e, hef, hKe, _, hes, heis⟩ := exists_smoothChart_near_compact f
    (isCompact_closedBall (0 : E2) 1) isOpen_univ (subset_univ _)
    hfs.contDiffOn hinj hregular
  exact ⟨hfs, ⟨eps, heps, hpole⟩, hseam, hboundary, himage, e, hef, hKe, hes, heis⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
