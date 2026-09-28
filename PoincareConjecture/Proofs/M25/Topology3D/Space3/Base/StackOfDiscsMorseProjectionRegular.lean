import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProjection
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D



theorem stackMorseProjection_regular
    (rFlat rOne v0 v1 rho lambda : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1)
    (hrho : 0 < rho) (hlambda : 0 < lambda) (hsmall : lambda < rho ^ 2 / 2) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
    let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
    let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
    let h : E2 → ℝ := fun x => rho ^ 2 + lambda * (C x).2
    let f : E2 → E2 := fun x => Real.sqrt (h x) • (C x).1
    (∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ ball (0 : E2) eps,
      h x = rho ^ 2 - lambda ∧
      f x = (2 * Real.sqrt (rho ^ 2 - lambda) / (1 + ‖x‖ ^ 2)) • x) ∧
      (∀ x : E2, |v x| < v0 →
        h x = rho ^ 2 + lambda * v x ∧ ‖f x‖ ^ 2 = h x) ∧
      HasFDerivAt f
        ((2 * Real.sqrt (rho ^ 2 - lambda)) • ContinuousLinearMap.id ℝ E2) 0 ∧
      ∀ x ∈ closedBall (0 : E2) 1,
        ∃ A : E2 ≃L[ℝ] E2, HasFDerivAt f (A : E2 →L[ℝ] E2) x := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
  let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
  let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
  let h : E2 → ℝ := fun x => rho ^ 2 + lambda * (C x).2
  let f : E2 → E2 := fun x => Real.sqrt (h x) • (C x).1
  let R := fun t => (stackCanonicalMeridian rFlat rOne v0 v1 t).1
  let Z := fun t => (stackCanonicalMeridian rFlat rOne v0 v1 t).2
  let w := fun t => Real.sqrt (rho ^ 2 + lambda * Z t) * R t
  obtain ⟨_, _, _, _, _, hcoords, _, hbounds, _, _, _, _⟩ :=
    stackMorseProjection_geometry rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  obtain ⟨_, hapos, _, _, hanear, hafar, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨_, _, _, _, hbfar, _⟩ :=
    stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  obtain ⟨_, hwm1, _, _, hwd, hmono, _⟩ :=
    stackMorseMeridian_geometry rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  obtain ⟨hroot, ⟨vPole, hpole0, hpole1, hpole⟩, _⟩ :=
    stackMorseMeridian_pole_and_seam rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  have hD (x : E2) : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hC1 (x : E2) : (C x).1 =
      (a (v x) * (2 / (1 + ‖x‖ ^ 2))) • x := (hcoords x).2.2.2.1
  have hC2 (x : E2) : (C x).2 = Z (v x) := (hcoords x).2.2.2.2.1
  have hCn (x : E2) : ‖(C x).1‖ = R (v x) := (hcoords x).2.2.2.2.2.1
  have hfn (x : E2) : ‖f x‖ = w (v x) := (hcoords x).2.2.2.2.2.2
  have hvc : Continuous v :=
    ((continuous_norm.pow 2).sub continuous_const).div
      (continuous_const.add (continuous_norm.pow 2)) (fun x => (hD x).ne')
  have hVp : IsOpen {x : E2 | v x < vPole} := isOpen_lt hvc continuous_const
  have h0p : (0 : E2) ∈ {x | v x < vPole} := by
    change v 0 < vPole
    simpa only [v, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_sub,
      add_zero, div_one] using hpole0
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hVp 0 h0p
  have hpf (x : E2) (hx : x ∈ ball (0 : E2) eps) :
      h x = rho ^ 2 - lambda ∧
      f x = (2 * Real.sqrt (rho ^ 2 - lambda) / (1 + ‖x‖ ^ 2)) • x := by
    have hvp : v x ∈ Icc (-1 : ℝ) vPole := ⟨(hcoords x).1, (hball hx).le⟩
    have hvneg : v x < 0 := (hball hx).trans (hpole1.trans (by linarith only [hv0, hv01]))
    have hax : a (v x) = 1 := hafar _ (by
      rw [abs_of_neg hvneg]
      have ht : v x < -v1 := (hball hx).trans hpole1
      linarith only [ht])
    have hcx : (C x).2 = -1 := (hC2 x).trans (hpole _ hvp).2.1
    have hh : h x = rho ^ 2 - lambda := by
      dsimp only [h]
      rw [hcx, mul_neg_one, ← sub_eq_add_neg]
    refine ⟨hh, ?_⟩
    dsimp only [f]
    rw [hh, hC1, hax, one_mul, smul_smul]
    congr 1
    ring
  have hseam (x : E2) (hx : |v x| < v0) :
      h x = rho ^ 2 + lambda * v x ∧ ‖f x‖ ^ 2 = h x := by
    have hvabs : |v x| < 1 := hx.trans (hv01.trans hv1)
    have hv2 : v x ^ 2 < 1 := by
      simpa only [sq_abs, one_pow] using
        (sq_lt_sq₀ (abs_nonneg (v x)) zero_le_one).mpr hvabs
    have hs : 0 < Real.sqrt (1 - v x ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hv2)
    have hcn : ‖(C x).1‖ = 1 := by
      rw [hCn]
      change a (v x) * Real.sqrt (1 - v x ^ 2) = 1
      have ha : a (v x) = (Real.sqrt (1 - v x ^ 2))⁻¹ := hanear _ hx.le
      rw [ha, inv_mul_cancel₀ hs.ne']
    have hcf : (C x).2 = b (C x).1 * v x := by
      rw [hC2]
      change stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2) (R (v x) ^ 2) * v x = _
      rw [← hCn]
      rfl
    have hcz : (C x).2 = v x := by
      have hb : b (C x).1 = 1 := hbfar _ (by rw [hcn]; exact hrOne.le)
      rw [hcf, hb, one_mul]
    have hh : h x = rho ^ 2 + lambda * v x := by dsimp only [h]; rw [hcz]
    have hpos : 0 < h x := by
      rw [hh]
      have hvlo : -1 < v x := (abs_lt.mp hvabs).1
      have ht := mul_lt_mul_of_pos_left hvlo hlambda
      nlinarith only [ht, hsmall, hlambda]
    refine ⟨hh, ?_⟩
    dsimp only [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      hcn, mul_one, Real.sq_sqrt hpos.le]
  let k : E2 → ℝ := fun x =>
    2 * Real.sqrt (rho ^ 2 - lambda) / (1 + ‖x‖ ^ 2)
  have hks : ContDiff ℝ ∞ k :=
    contDiff_const.div (contDiff_const.add (contDiff_id.norm_sq ℝ))
      (fun x => (hD x).ne')
  have hpd : HasFDerivAt f
      ((2 * Real.sqrt (rho ^ 2 - lambda)) • ContinuousLinearMap.id ℝ E2) 0 := by
    have hkder : HasFDerivAt k (fderiv ℝ k 0) 0 :=
      (hks.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hd : HasFDerivAt (fun x : E2 => k x • x)
        (k 0 • ContinuousLinearMap.id ℝ E2 + (fderiv ℝ k 0).smulRight (0 : E2)) 0 :=
      hkder.fun_smul (hasFDerivAt_id (0 : E2))
    have hd' : HasFDerivAt (fun x : E2 => k x • x)
        ((2 * Real.sqrt (rho ^ 2 - lambda)) • ContinuousLinearMap.id ℝ E2) 0 := by
      simpa only [k, id_eq, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero,
        div_one, ContinuousLinearMap.smulRight_zero, add_zero] using hd
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E2) heps] with x hx
    exact (hpf x hx).2
  have hequiv (L : E2 →L[ℝ] E2) (hi : Function.Injective L) :
      ∃ A : E2 ≃L[ℝ] E2, (A : E2 →L[ℝ] E2) = L := by
    let A := (LinearEquiv.ofBijective L.toLinearMap
      ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
    exact ⟨A, by ext z; rfl⟩
  refine ⟨⟨eps, heps, hpf⟩, hseam, hpd, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hp : 0 < 2 * Real.sqrt (rho ^ 2 - lambda) := mul_pos (by norm_num) hroot
    obtain ⟨A, hA⟩ := hequiv
      ((2 * Real.sqrt (rho ^ 2 - lambda)) • ContinuousLinearMap.id ℝ E2) (by
        intro y z he
        change (2 * Real.sqrt (rho ^ 2 - lambda)) • y =
          (2 * Real.sqrt (rho ^ 2 - lambda)) • z at he
        have ht := congrArg (fun w : E2 => (2 * Real.sqrt (rho ^ 2 - lambda))⁻¹ • w) he
        simpa only [smul_smul, inv_mul_cancel₀ hp.ne', one_smul] using ht)
    exact ⟨A, hA ▸ hpd⟩
  let r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx0
  have hrt : r ≤ 1 := mem_closedBall_zero_iff.mp hx
  let nu : ℝ → ℝ := fun t => (t ^ 2 - 1) / (1 + t ^ 2)
  let eta : ℝ → ℝ := fun t => w (nu t) / t
  have hnu : nu r = v x := rfl
  have ht : v x ∈ Ioc (-1 : ℝ) 0 := by
    refine ⟨?_, (hbounds x hx).1.2⟩
    apply (lt_div_iff₀ (hD x)).mpr
    nlinarith only [sq_pos_of_pos hr]
  have hwD : HasDerivAt w (deriv w (v x)) (v x) := (hwd _ ht).1.differentiableAt.hasDerivAt
  have hwp : 0 < w (v x) := by
    have hh := hmono (by simp : (-1 : ℝ) ∈ Icc (-1 : ℝ) 0) ⟨ht.1.le, ht.2⟩ ht.1
    rwa [hwm1] at hh
  let beta := w (v x) / r
  let d := deriv w (v x) * (4 * r / (1 + r ^ 2) ^ 2)
  let delta := (d - beta) / r ^ 2
  have hbeta : 0 < beta := div_pos hwp hr
  have hdpos : 0 < d := mul_pos (hwd _ ht).2
    (div_pos (mul_pos (by norm_num) hr) (sq_pos_of_pos (by positivity)))
  have hnud : HasDerivAt nu (4 * r / (1 + r ^ 2) ^ 2) r := by
    have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
      simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using hasDerivAt_pow 2 r
    exact ((hp.sub_const 1).div (hp.const_add 1) (by positivity)).congr_deriv (by ring)
  have hcomp : HasDerivAt (fun t => w (nu t)) d r := by
    have hh : HasDerivAt w (deriv w (v x)) (nu r) := by rw [hnu]; exact hwD
    exact hh.comp r hnud
  have hetad : HasDerivAt eta ((d - beta) / r) r := by
    apply (hcomp.div (hasDerivAt_id r) hr.ne').congr_deriv
    dsimp only [beta]
    rw [hnu]
    simp only [id_eq]
    field_simp [hr.ne']
  have hnormd : HasFDerivAt (fun y : E2 => ‖y‖) (r⁻¹ • innerSL ℝ x) x := by
    have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by
      change ‖x‖ ^ 2 ≠ 0
      exact (sq_pos_of_pos hr).ne')
    have hn' : HasFDerivAt (fun y : E2 => ‖y‖)
        ((1 / (2 * r)) • (2 • innerSL ℝ x)) x := by
      simpa only [Real.sqrt_sq (norm_nonneg _)] using hn
    apply hn'.congr_fderiv
    ext z
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    field_simp [hr.ne']
    ring
  let D : E2 →L[ℝ] E2 :=
    beta • ContinuousLinearMap.id ℝ E2 + (delta • innerSL ℝ x).smulRight x
  have hc : ((d - beta) / r) • (r⁻¹ • innerSL ℝ x) = delta • innerSL ℝ x := by
    rw [smul_smul]
    congr 1
    dsimp only [delta]
    field_simp [hr.ne']
  have hradial (y : E2) (hy : y ≠ 0) : f y = eta ‖y‖ • y := by
    let c := Real.sqrt (h y) * a (v y) * (2 / (1 + ‖y‖ ^ 2))
    have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hapos _).le)
      (div_pos (by norm_num) (hD y)).le
    have hf : f y = c • y := by
      dsimp only [f, c]
      rw [hC1, smul_smul]
      congr 1
      ring
    have hn : c * ‖y‖ = w (v y) := by
      have he := hfn y
      rwa [hf, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0] at he
    have he : eta ‖y‖ = c := by
      change w (v y) / ‖y‖ = c
      rw [← hn, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hy)]
    rw [he]
    exact hf
  have hDf : HasFDerivAt f D x := by
    have he := (hetad.comp_hasFDerivAt x hnormd).smul (hasFDerivAt_id x)
    change HasFDerivAt (fun y : E2 => eta ‖y‖ • y)
      (beta • ContinuousLinearMap.id ℝ E2 +
        (((d - beta) / r) • (r⁻¹ • innerSL ℝ x)).smulRight x) x at he
    rw [hc] at he
    apply he.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    exact hradial y hy
  have hDz (z : E2) : D z = beta • z + (delta * ⟪x, z⟫_ℝ) • x := rfl
  have hker (z : E2) (hz : D z = 0) : z = 0 := by
    have hh := congrArg (fun y : E2 => ⟪x, y⟫_ℝ) hz
    rw [hDz, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, inner_zero_right] at hh
    have he : beta * ⟪x, z⟫_ℝ + (delta * ⟪x, z⟫_ℝ) * ‖x‖ ^ 2 =
        d * ⟪x, z⟫_ℝ := by
      change beta * ⟪x, z⟫_ℝ + (delta * ⟪x, z⟫_ℝ) * r ^ 2 = _
      dsimp only [delta]
      field_simp [hr.ne']
      ring
    rw [he] at hh
    have hin : ⟪x, z⟫_ℝ = 0 := (mul_eq_zero.mp hh).resolve_left hdpos.ne'
    rw [hDz, hin, mul_zero, zero_smul, add_zero] at hz
    exact (smul_eq_zero.mp hz).resolve_left hbeta.ne'
  have hi : Function.Injective D := by
    intro y z hyz
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hyz, sub_self]
  obtain ⟨A, hA⟩ := hequiv D hi
  exact ⟨A, hA ▸ hDf⟩

end PoincareConjecture.M25.Topology3D
