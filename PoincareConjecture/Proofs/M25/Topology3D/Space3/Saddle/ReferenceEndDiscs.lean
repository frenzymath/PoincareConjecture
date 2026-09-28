import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1500000 in

theorem exists_nonnested_reference_end_disc_charts
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2) :
    let eps : Fin 2 → ℝ := ![1, -1]
    let R0 : ℝ := Real.sqrt (1 / 8)
    let C : ℝ := 3 / 4
    let g : ℝ → ℝ := fun y => y * Real.sqrt (2 + y ^ 2)
    let k : ℝ → ℝ := fun Y =>
      Real.sqrt 2 * Y / Real.sqrt (2 + Real.sqrt (4 + 4 * Y ^ 2))
    let Xi : E2 → ℝ := fun x => Real.sqrt C * (J2 x).1
    let Eta : E2 → ℝ := fun x => k (Real.sqrt C * (J2 x).2)
    let f : UnitTwoSphere → ℝ := fun p =>
      1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
        d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
    ∃ (eMinus : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere)
      (ePlus : OpenPartialHomeomorph E2 UnitTwoSphere),
      (∀ i : Fin 2,
        (eMinus i).source = ball (0 : E2) (3 / (8 * R0)) ∧
        (eMinus i).target = {p : UnitTwoSphere |
          0 < eps i * (p : E3) 1 ∧
          ((p : E3) 0) ^ 2 + ((p : E3) 2 + 1 / 2) ^ 2 < (3 / 8) ^ 2} ∧
        ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ (eMinus i) (eMinus i).source ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ (eMinus i).symm (eMinus i).target ∧
        (∀ x ∈ (eMinus i).source,
          (eMinus i x : E3) =
            !₂[R0 * (J2 x).1,
              eps i * Real.sqrt (3 / 4 + R0 * (J2 x).2 -
                R0 ^ 2 * ((J2 x).1 ^ 2 + (J2 x).2 ^ 2)),
              R0 * (J2 x).2 - 1 / 2]) ∧
        (∀ p ∈ (eMinus i).target, (eMinus i).symm p =
          J2.symm ((p : E3) 0 / R0, ((p : E3) 2 + 1 / 2) / R0)) ∧
        closedBall (0 : E2) 1 ⊆ (eMinus i).source ∧
        (∀ x ∈ (eMinus i).source,
          f (eMinus i x) = -1 / 4 + R0 ^ 2 * ‖x‖ ^ 2) ∧
        (eMinus i) '' ball (0 : E2) 1 =
          {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧ f p < -1 / 8} ∧
        (eMinus i) '' closedBall (0 : E2) 1 =
          {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧ f p ≤ -1 / 8} ∧
        (eMinus i) '' sphere (0 : E2) 1 =
          {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧ f p = -1 / 8}) ∧
      ePlus.source = ball (0 : E2) (9 / 8) ∧
      ePlus.target = {p : UnitTwoSphere | 0 < (p : E3) 2 ∧
        (((p : E3) 0) ^ 2 + 2 * ((p : E3) 1) ^ 2 + ((p : E3) 1) ^ 4) / C <
          (9 / 8) ^ 2} ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ePlus ePlus.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ePlus.symm ePlus.target ∧
      (∀ x ∈ ePlus.source, (ePlus x : E3) =
        !₂[Xi x, Eta x, Real.sqrt (1 - (Xi x) ^ 2 - (Eta x) ^ 2)]) ∧
      (∀ p ∈ ePlus.target, ePlus.symm p =
        J2.symm ((p : E3) 0 / Real.sqrt C, g ((p : E3) 1) / Real.sqrt C)) ∧
      closedBall (0 : E2) 1 ⊆ ePlus.source ∧
      ePlus '' ball (0 : E2) 1 = {p : UnitTwoSphere | 3 / 2 < f p} ∧
      ePlus '' closedBall (0 : E2) 1 = {p : UnitTwoSphere | 3 / 2 ≤ f p} ∧
      ePlus '' sphere (0 : E2) 1 = {p : UnitTwoSphere | f p = 3 / 2} ∧
      Disjoint ((eMinus 0) '' closedBall (0 : E2) 1)
        ((eMinus 1) '' closedBall (0 : E2) 1) ∧
      (∀ i : Fin 2, Disjoint ((eMinus i) '' closedBall (0 : E2) 1)
        (ePlus '' closedBall (0 : E2) 1)) ∧
      ∀ p : UnitTwoSphere, (f p = -1 / 8 ∨ f p = 3 / 2) →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
  classical
  dsimp only
  let eps : Fin 2 → ℝ := ![1, -1]
  let R0 : ℝ := Real.sqrt (1 / 8)
  let C : ℝ := 3 / 4
  let g : ℝ → ℝ := fun y => y * Real.sqrt (2 + y ^ 2)
  let k : ℝ → ℝ := fun Y =>
    Real.sqrt 2 * Y / Real.sqrt (2 + Real.sqrt (4 + 4 * Y ^ 2))
  let Xi : E2 → ℝ := fun x => Real.sqrt C * (J2 x).1
  let Eta : E2 → ℝ := fun x => k (Real.sqrt C * (J2 x).2)
  let f : UnitTwoSphere → ℝ := fun p =>
    1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
      d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hR : 0 < R0 := Real.sqrt_pos.2 (by norm_num)
  have hR2 : R0 ^ 2 = 1 / 8 := Real.sq_sqrt (by norm_num)
  have hC : 0 < C := by norm_num [C]
  have hCroot : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hC2 : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
  have heps (i : Fin 2) : eps i ^ 2 = 1 := by fin_cases i <;> norm_num [eps]
  have hsphere (p : UnitTwoSphere) :
      ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2 + ((p : E3) 2) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (norm_eq_of_mem_sphere p)
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, one_pow] using h
  have hnorm3 (v : E3) (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by
      simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] using hv
    nlinarith [norm_nonneg v]
  have hb (x : E2) (r : ℝ) (hr : 0 < r) :
      x ∈ ball (0 : E2) r ↔ ‖x‖ ^ 2 < r ^ 2 := by
    simpa only [mem_ball, dist_zero_right] using
      (sq_lt_sq₀ (norm_nonneg x) hr.le).symm
  have hc (x : E2) : x ∈ closedBall (0 : E2) 1 ↔ ‖x‖ ^ 2 ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right, one_pow] using
      (sq_le_sq₀ (norm_nonneg x) zero_le_one).symm
  have hs (x : E2) : x ∈ sphere (0 : E2) 1 ↔ ‖x‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm]; constructor <;> intro h
    · rw [h]; norm_num
    · nlinarith [norm_nonneg x]
  have hcoord (j : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p : UnitTwoSphere => (p : E3) j) :=
    (EuclideanSpace.proj j).contDiff.contMDiff.comp contMDiff_coe_sphere
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    ((contMDiff_const.add (hcoord 2)).sub ((hcoord 1).pow 2)).add
      (hd.contMDiff.comp (((hcoord 0).pow 2).add ((hcoord 1).pow 2)))
  have hJx : ContDiff ℝ ∞ (fun x : E2 => (J2 x).1) := J2.contDiff.fst
  have hJy : ContDiff ℝ ∞ (fun x : E2 => (J2 x).2) := J2.contDiff.snd
  have direction (v : E3) (hv : ‖v‖ = 1) : (sphereDirection v : E3) = v := by
    rw [sphereDirection_coe (by intro h; simp [h] at hv),
      NormedSpace.normalize_eq_self_of_norm_eq_one hv]

  have buildChart (U : Set E2) (V : Set UnitTwoSphere) (hU : IsOpen U)
      (hV : IsOpen V) (G : E2 → E3) (H : UnitTwoSphere → E2)
      (hG : ContDiffOn ℝ ∞ G U) (hH : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ H)
      (hunit : ∀ x ∈ U, ‖G x‖ = 1)
      (hmap : ∀ x ∈ U, sphereDirection (G x) ∈ V)
      (hback : ∀ p ∈ V, H p ∈ U)
      (hleft : ∀ x ∈ U, H (sphereDirection (G x)) = x)
      (hright : ∀ p ∈ V, G (H p) = (p : E3)) :
      ∃ e : OpenPartialHomeomorph E2 UnitTwoSphere,
        e.source = U ∧ e.target = V ∧
        ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
        (∀ x ∈ U, (e x : E3) = G x) ∧ (∀ p, e.symm p = H p) := by
    have hF : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ (sphereDirection ∘ G) U :=
      contMDiffOn_sphere_of_coe hU _
        (hG.congr (fun x hx => direction (G x) (hunit x hx))).contMDiffOn
    let e : OpenPartialHomeomorph E2 UnitTwoSphere :=
      { toFun := sphereDirection ∘ G, invFun := H, source := U, target := V
        map_source' := hmap, map_target' := hback, left_inv' := hleft
        right_inv' := fun p hp => Subtype.ext (by
          change (sphereDirection (G (H p)) : E3) = (p : E3)
          rw [direction (G (H p)) (hunit _ (hback p hp)), hright p hp])
        open_source := hU, open_target := hV
        continuousOn_toFun := hF.continuousOn
        continuousOn_invFun := hH.continuous.continuousOn }
    exact ⟨e, rfl, rfl, hF, hH.contMDiffOn,
      fun x hx => direction (G x) (hunit x hx), fun _ => rfl⟩
  let lowerRadius : ℝ := 3 / (8 * R0)
  have hlpos : 0 < lowerRadius := by dsimp [lowerRadius]; positivity
  have hlrad : R0 ^ 2 * lowerRadius ^ 2 = 9 / 64 := by
    dsimp [lowerRadius]; field_simp [hR.ne']; ring
  have hlone : 1 < lowerRadius := by
    by_contra hn
    have hsq := (sq_le_sq₀ hlpos.le zero_le_one).2 (le_of_not_gt hn)
    nlinarith [mul_nonneg (sq_nonneg R0) (sub_nonneg.mpr hsq)]
  let L : E2 → ℝ := fun x =>
    3 / 4 + R0 * (J2 x).2 - R0 ^ 2 * ((J2 x).1 ^ 2 + (J2 x).2 ^ 2)
  have hscale (x : E2) : (R0 * (J2 x).1) ^ 2 + (R0 * (J2 x).2) ^ 2 =
      R0 ^ 2 * ‖x‖ ^ 2 := by rw [← hJ2]; ring
  have hL (x : E2) (hx : x ∈ ball (0 : E2) lowerRadius) :
      0 < L x ∧ sigma < (R0 * (J2 x).1) ^ 2 + L x := by
    have hsq := (hb x lowerRadius hlpos).1 hx
    have hz : R0 ^ 2 * ‖x‖ ^ 2 < 9 / 64 := by
      nlinarith [mul_pos (sq_pos_of_pos hR) (sub_pos.mpr hsq)]
    have hy : -3 / 8 < R0 * (J2 x).2 := by
      nlinarith [sq_nonneg (R0 * (J2 x).1), hscale x]
    dsimp [L]
    rw [hJ2]
    constructor <;> nlinarith only [hy, hz, hsigmaSmall, sq_nonneg (R0 * (J2 x).1)]
  let GM (i : Fin 2) (x : E2) : E3 :=
    !₂[R0 * (J2 x).1, eps i * Real.sqrt (L x), R0 * (J2 x).2 - 1 / 2]
  let HM (p : UnitTwoSphere) : E2 :=
    J2.symm ((p : E3) 0 / R0, ((p : E3) 2 + 1 / 2) / R0)
  let VM (i : Fin 2) : Set UnitTwoSphere := {p |
    0 < eps i * (p : E3) 1 ∧
      ((p : E3) 0) ^ 2 + ((p : E3) 2 + 1 / 2) ^ 2 < (3 / 8) ^ 2}
  have hHM : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ HM :=
    J2.symm.contDiff.contMDiff.comp
      (((hcoord 0).div_const R0).prodMk_space
        (((hcoord 2).add contMDiff_const).div_const R0))
  have hHMnorm (p : UnitTwoSphere) :
      R0 ^ 2 * ‖HM p‖ ^ 2 = ((p : E3) 0) ^ 2 + ((p : E3) 2 + 1 / 2) ^ 2 := by
    rw [← hJ2]; simp only [HM, ContinuousLinearEquiv.apply_symm_apply]
    field_simp [hR.ne']
  have hGMunit (i : Fin 2) (x : E2) (hx : x ∈ ball (0 : E2) lowerRadius) :
      ‖GM i x‖ = 1 := by
    apply hnorm3; dsimp [GM]
    simp only [mul_pow, Real.sq_sqrt (hL x hx).1.le, heps i, one_mul]
    dsimp [L]; ring
  have hGMsmooth (i : Fin 2) : ContDiffOn ℝ ∞ (GM i) (ball 0 lowerRadius) := by
    have hLs : ContDiff ℝ ∞ L := by dsimp [L]; fun_prop
    apply (contDiffOn_piLp 2).2; intro j; fin_cases j
    · exact (contDiff_const.mul hJx).contDiffOn
    · exact contDiffOn_const.mul (hLs.contDiffOn.sqrt (fun x hx => (hL x hx).1.ne'))
    · exact ((contDiff_const.mul hJy).sub contDiff_const).contDiffOn
  have hGMtarget (i : Fin 2) (x : E2) (hx : x ∈ ball (0 : E2) lowerRadius) :
      sphereDirection (GM i x) ∈ VM i := by
    change 0 < eps i * (sphereDirection (GM i x) : E3) 1 ∧ _
    rw [direction _ (hGMunit i x hx)]; dsimp [GM]
    have hsq := (hb x lowerRadius hlpos).1 hx
    constructor
    · nlinarith [heps i, Real.sqrt_pos.2 (hL x hx).1]
    · nlinarith [hscale x, mul_pos (sq_pos_of_pos hR) (sub_pos.mpr hsq)]
  have hGMback (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ VM i) :
      HM p ∈ ball (0 : E2) lowerRadius := by
    apply (hb _ _ hlpos).2
    apply (mul_lt_mul_iff_of_pos_left (sq_pos_of_pos hR)).mp
    rw [hHMnorm, hlrad]
    simpa only [show (3 / 8 : ℝ) ^ 2 = 9 / 64 by norm_num] using hp.2
  have hGMright (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ VM i) :
      GM i (HM p) = (p : E3) := by
    have hp' : 0 < eps i * (p : E3) 1 := hp.1
    have hLs : L (HM p) = ((p : E3) 1) ^ 2 := by
      have he : L (HM p) = 3 / 4 + ((p : E3) 2 + 1 / 2) -
          ((p : E3) 0) ^ 2 - ((p : E3) 2 + 1 / 2) ^ 2 := by
        dsimp [L, HM]; simp only [ContinuousLinearEquiv.apply_symm_apply]
        field_simp [hR.ne']; ring
      rw [he]; nlinarith [hsphere p]
    ext j; fin_cases j
    · change R0 * (J2 (HM p)).1 = (p : E3) 0
      simp only [HM, ContinuousLinearEquiv.apply_symm_apply]
      field_simp [hR.ne']
    · change eps i * Real.sqrt (L (HM p)) = (p : E3) 1
      rw [hLs, Real.sqrt_sq_eq_abs]
      fin_cases i <;> norm_num [eps] at hp' ⊢
      · exact hp'.le
      · rw [abs_of_neg (by linarith)]; ring
    · change R0 * (J2 (HM p)).2 - 1 / 2 = (p : E3) 2
      simp only [HM, ContinuousLinearEquiv.apply_symm_apply]
      field_simp [hR.ne']
      ring
  have hGMleft (i : Fin 2) (x : E2) (hx : x ∈ ball (0 : E2) lowerRadius) :
      HM (sphereDirection (GM i x)) = x := by
    dsimp [HM]; rw [direction _ (hGMunit i x hx)]
    apply J2.injective; simp [GM, hR.ne']
  have hVMopen (i : Fin 2) : IsOpen (VM i) :=
    (isOpen_lt continuous_const (continuous_const.mul (hcoord 1).continuous)).inter
      (isOpen_lt (((hcoord 0).continuous.pow 2).add
        (((hcoord 2).continuous.add continuous_const).pow 2)) continuous_const)
  choose eM heMs heMt heMd heMi heMf heMinv using
    fun i => buildChart (ball 0 lowerRadius) (VM i) isOpen_ball (hVMopen i)
      (GM i) HM (hGMsmooth i) hHM (hGMunit i) (hGMtarget i)
      (hGMback i) (hGMleft i) (hGMright i)
  have hMclosed (i : Fin 2) : closedBall (0 : E2) 1 ⊆ (eM i).source := by
    rw [heMs]; exact closedBall_subset_ball hlone
  have hMheight (i : Fin 2) (x : E2) (hx : x ∈ (eM i).source) :
      f (eM i x) = -1 / 4 + R0 ^ 2 * ‖x‖ ^ 2 := by
    have hx' := hx; rw [heMs] at hx'
    have hsq := Real.sq_sqrt (hL x hx').1.le
    have hq : sigma ≤ (GM i x) 0 ^ 2 + (GM i x) 1 ^ 2 := by
      dsimp [GM]; simp only [mul_pow, heps i, hsq, one_mul]
      simpa only [mul_pow] using (hL x hx').2.le
    dsimp [f]; rw [heMf i x hx', hdZero _ hq]
    dsimp [GM]; simp only [mul_pow, heps i, hsq, one_mul]
    dsimp [L]; rw [hJ2]; ring
  have hMtarget (i : Fin 2) (p : UnitTwoSphere)
      (hsgn : 0 < eps i * (p : E3) 1) (hp : f p ≤ -1 / 8) : p ∈ (eM i).target := by
    let q : ℝ := ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hw : -1 ≤ (p : E3) 2 := by
      nlinarith [hsphere p, sq_nonneg ((p : E3) 0), sq_nonneg ((p : E3) 1)]
    have hq : sigma < q := by
      by_contra hn
      have hsmall : q ≤ 1 / 16 := (le_of_not_gt hn).trans hsigmaSmall
      have hq2 : q ^ 2 ≤ 1 / 256 := by
        have hb := (sq_le_sq₀ hq0 (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hsmall
        norm_num at hb ⊢
        exact hb
      have hdq := (hdBounds q hq0).1
      dsimp [f, q] at *; nlinarith [sq_nonneg ((p : E3) 0)]
    have hz : d q = 0 := hdZero q hq.le
    have hh : ((p : E3) 0) ^ 2 + ((p : E3) 2 + 1 / 2) ^ 2 = f p + 1 / 4 := by
      dsimp [f]; change _ = 1 + _ - _ + d q + _; rw [hz]; nlinarith [hsphere p]
    rw [heMt]; exact ⟨hsgn, by nlinarith⟩
  have hMimages (i : Fin 2) :
      eM i '' ball (0 : E2) 1 = {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧
        f p < -1 / 8} ∧
      eM i '' closedBall (0 : E2) 1 = {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧
        f p ≤ -1 / 8} ∧
      eM i '' sphere (0 : E2) 1 = {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧
        f p = -1 / 8} := by
    have hforward (x : E2) (hx : x ∈ closedBall 0 1) : 0 < eps i * (eM i x : E3) 1 := by
      have ht := (eM i).map_source (hMclosed i hx); rw [heMt] at ht; exact ht.1
    have hback (p : UnitTwoSphere) (hp : p ∈ (eM i).target) :
        f p = -1 / 4 + R0 ^ 2 * ‖(eM i).symm p‖ ^ 2 := by
      simpa only [(eM i).right_inv hp] using hMheight i _ ((eM i).map_target hp)
    refine ⟨?_, ?_, ?_⟩ <;> ext p <;> constructor
    · rintro ⟨x, hx, rfl⟩; refine ⟨hforward x (ball_subset_closedBall hx), ?_⟩
      rw [hMheight i x (hMclosed i (ball_subset_closedBall hx)), hR2]
      have := (hb x 1 zero_lt_one).1 hx; norm_num only [one_pow] at this; linarith
    · intro hp; have ht := hMtarget i p hp.1 hp.2.le
      refine ⟨(eM i).symm p, (hb _ 1 zero_lt_one).2 ?_, (eM i).right_inv ht⟩
      have := hback p ht; rw [hR2] at this
      norm_num only [one_pow]; linarith [hp.2]
    · rintro ⟨x, hx, rfl⟩; refine ⟨hforward x hx, ?_⟩
      rw [hMheight i x (hMclosed i hx), hR2]; have := (hc x).1 hx; linarith
    · intro hp; have ht := hMtarget i p hp.1 hp.2
      refine ⟨(eM i).symm p, (hc _).2 ?_, (eM i).right_inv ht⟩
      have := hback p ht; rw [hR2] at this; linarith [hp.2]
    · rintro ⟨x, hx, rfl⟩; have hn := (hs x).1 hx
      refine ⟨hforward x ((hc x).2 hn.le), ?_⟩
      rw [hMheight i x (hMclosed i ((hc x).2 hn.le)), hn, hR2]; norm_num
    · intro hp; have ht := hMtarget i p hp.1 hp.2.le
      refine ⟨(eM i).symm p, (hs _).2 ?_, (eM i).right_inv ht⟩
      have := hback p ht; rw [hR2] at this; linarith [hp.2]

  have hg : ContDiff ℝ ∞ g :=
    contDiff_id.mul ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun y => by positivity))
  have hk : ContDiff ℝ ∞ k := by
    dsimp [k]; apply (contDiff_const.mul contDiff_id).div
    · exact (contDiff_const.add ((contDiff_const.add
        (contDiff_const.mul (contDiff_id.pow 2))).sqrt (fun y => by positivity))).sqrt
        (fun y => by positivity)
    · intro y; positivity
  have hkg (y : ℝ) : k (g y) = y := by
    have hs2 : 0 < Real.sqrt (2 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hsq := Real.sq_sqrt (show 0 ≤ 2 + y ^ 2 by positivity)
    have hinner : Real.sqrt (4 + 4 * (g y) ^ 2) = 2 + 2 * y ^ 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      dsimp [g]; rw [mul_pow, hsq]; ring
    have houter : Real.sqrt (2 + (2 + 2 * y ^ 2)) =
        Real.sqrt 2 * Real.sqrt (2 + y ^ 2) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
    dsimp [k]; rw [hinner, houter]; dsimp [g]
    field_simp [hs2.ne', (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
  have hgk (Y : ℝ) : g (k Y) = Y := by
    let S := Real.sqrt (4 + 4 * Y ^ 2)
    let B := Real.sqrt (2 + S)
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hS2 : S ^ 2 = 4 + 4 * Y ^ 2 := Real.sq_sqrt (by positivity)
    have hSlo : 2 ≤ S := by nlinarith
    have hB : 0 < B := Real.sqrt_pos.2 (by positivity)
    have hB2 : B ^ 2 = 2 + S := Real.sq_sqrt (by positivity)
    have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hk2 : (k Y) ^ 2 = (S - 2) / 2 := by
      dsimp [k]; change (Real.sqrt 2 * Y / B) ^ 2 = _
      rw [div_pow, mul_pow, htwo, hB2]
      apply (div_eq_iff (show 2 + S ≠ 0 by positivity)).2
      nlinarith
    have hout : Real.sqrt (2 + (k Y) ^ 2) = B / Real.sqrt 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      rw [hk2, div_pow, htwo, hB2]; ring
    dsimp [g]; rw [hout]; change (Real.sqrt 2 * Y / B) * (B / Real.sqrt 2) = Y
    field_simp [hB.ne', (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
  have hg2 (y : ℝ) : (g y) ^ 2 = 2 * y ^ 2 + y ^ 4 := by
    dsimp [g]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hX : ContDiff ℝ ∞ Xi := contDiff_const.mul hJx
  have hY : ContDiff ℝ ∞ Eta := hk.comp (contDiff_const.mul hJy)
  have hXY (x : E2) : Xi x ^ 2 + 2 * Eta x ^ 2 + Eta x ^ 4 = C * ‖x‖ ^ 2 := by
    have hh := hg2 (Eta x)
    have hgEta : g (Eta x) = Real.sqrt C * (J2 x).2 := hgk _
    rw [hgEta, mul_pow, hC2] at hh
    dsimp [Xi]; rw [mul_pow, hC2, ← hJ2]; nlinarith
  let GP (x : E2) : E3 := !₂[Xi x, Eta x, Real.sqrt (1 - Xi x ^ 2 - Eta x ^ 2)]
  let HP (p : UnitTwoSphere) : E2 :=
    J2.symm ((p : E3) 0 / Real.sqrt C, g ((p : E3) 1) / Real.sqrt C)
  let P (p : UnitTwoSphere) : ℝ :=
    ((p : E3) 0) ^ 2 + 2 * ((p : E3) 1) ^ 2 + ((p : E3) 1) ^ 4
  let VP : Set UnitTwoSphere := {p | 0 < (p : E3) 2 ∧ P p / C < (9 / 8) ^ 2}
  have hHP : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ HP :=
    J2.symm.contDiff.contMDiff.comp (((hcoord 0).div_const _).prodMk_space
      ((hg.contMDiff.comp (hcoord 1)).div_const _))
  have hHPnorm (p : UnitTwoSphere) : ‖HP p‖ ^ 2 = P p / C := by
    rw [← hJ2]; simp only [HP, ContinuousLinearEquiv.apply_symm_apply]
    rw [div_pow, div_pow, hC2, hg2]; dsimp [P]; ring
  have hGPpos (x : E2) (hx : x ∈ ball (0 : E2) (9 / 8)) :
      0 < 1 - Xi x ^ 2 - Eta x ^ 2 := by
    have hn := (hb x (9 / 8) (by norm_num)).1 hx
    have := hXY x; dsimp [C] at this
    nlinarith [sq_nonneg (Eta x), sq_nonneg (Eta x ^ 2)]
  have hGPunit (x : E2) (hx : x ∈ ball (0 : E2) (9 / 8)) : ‖GP x‖ = 1 := by
    apply hnorm3; dsimp [GP]; rw [Real.sq_sqrt (hGPpos x hx).le]; ring
  have hGPsmooth : ContDiffOn ℝ ∞ GP (ball (0 : E2) (9 / 8)) := by
    apply (contDiffOn_piLp 2).2; intro j; fin_cases j
    · exact hX.contDiffOn
    · exact hY.contDiffOn
    · exact ((contDiff_const.sub (hX.pow 2)).sub (hY.pow 2)).contDiffOn.sqrt
        (fun x hx => (hGPpos x hx).ne')
  have hVPopen : IsOpen VP :=
    (isOpen_lt continuous_const (hcoord 2).continuous).inter
      (isOpen_lt (((((hcoord 0).continuous.pow 2).add
        (continuous_const.mul ((hcoord 1).continuous.pow 2))).add
        ((hcoord 1).continuous.pow 4)).div_const C) continuous_const)
  obtain ⟨eP, hePs, hePt, hePd, hePi, hePf, hePinv⟩ :=
    buildChart (ball 0 (9 / 8)) VP isOpen_ball hVPopen GP HP hGPsmooth hHP hGPunit
      (by intro x hx; change 0 < (sphereDirection (GP x) : E3) 2 ∧ _
          dsimp only [P]
          rw [direction _ (hGPunit x hx)]; dsimp only [GP]
          refine ⟨Real.sqrt_pos.2 (hGPpos x hx), ?_⟩
          change (Xi x ^ 2 + 2 * Eta x ^ 2 + Eta x ^ 4) / C < (9 / 8) ^ 2
          rw [hXY, mul_div_cancel_left₀ _ hC.ne']; exact (hb x _ (by norm_num)).1 hx)
      (by intro p hp; apply (hb _ _ (by norm_num)).2; rw [hHPnorm]; exact hp.2)
      (by intro x hx; dsimp [HP]; rw [direction _ (hGPunit x hx)]
          apply J2.injective; simp only [ContinuousLinearEquiv.apply_symm_apply]
          dsimp [GP, Xi, Eta]; rw [hgk]; simp [hCroot.ne'])
      (by intro p hp; ext j; fin_cases j <;> dsimp [GP, Xi, Eta, HP]
          · simp only [ContinuousLinearEquiv.apply_symm_apply]
            field_simp
          · simp only [ContinuousLinearEquiv.apply_symm_apply, mul_div_cancel₀ _ hCroot.ne']
            exact hkg _
          · simp only [ContinuousLinearEquiv.apply_symm_apply, mul_div_cancel₀ _ hCroot.ne']
            rw [hkg]; exact (Real.sqrt_eq_iff_eq_sq
              (by nlinarith [hsphere p]) hp.1.le).2 (by nlinarith [hsphere p]))
  have hPclosed : closedBall (0 : E2) 1 ⊆ eP.source := by
    rw [hePs]; exact closedBall_subset_ball (by norm_num)
  have hupper (p : UnitTwoSphere) (hw : 0 < (p : E3) 2) :
      (P p < C ↔ 3 / 2 < f p) ∧ (P p ≤ C ↔ 3 / 2 ≤ f p) ∧
      (P p = C ↔ f p = 3 / 2) := by
    let q := ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    by_cases hsmall : q ≤ sigma
    · have hq : q ≤ 1 / 16 := hsmall.trans hsigmaSmall
      have hw1 : (p : E3) 2 ≤ 1 := by nlinarith [hsphere p, hq0]
      have hwq : 1 - q ≤ (p : E3) 2 := by
        have hh := mul_nonneg hw.le (sub_nonneg.mpr hw1)
        dsimp [q] at *; nlinarith [hsphere p]
      have hq2 : q ^ 2 ≤ 1 / 256 := by nlinarith
      have heta : ((p : E3) 1) ^ 2 ≤ q := by dsimp [q]; nlinarith [sq_nonneg ((p : E3) 0)]
      have heta4 : ((p : E3) 1) ^ 4 ≤ q ^ 2 := by
        nlinarith [sq_nonneg ((p : E3) 1), mul_nonneg hq0 (sub_nonneg.mpr heta)]
      have hP : P p < C := by dsimp [P, C]; dsimp [q] at *; nlinarith
      have hF : 3 / 2 < f p := by
        have hdq := (hdBounds q hq0).1
        dsimp [f]; change _ < 1 + _ - _ + d q; nlinarith
      exact ⟨iff_of_true hP hF, iff_of_true hP.le hF.le,
        iff_of_false (ne_of_lt hP) (ne_of_gt hF)⟩
    · have hz := hdZero q (le_of_not_ge hsmall)
      have hF : f p = 1 + (p : E3) 2 - ((p : E3) 1) ^ 2 := by
        dsimp [f]; change _ + d q = _; rw [hz]; ring
      let b : ℝ := 1 / 2 + ((p : E3) 1) ^ 2
      have hbase : 0 < b := by dsimp [b]; positivity
      have hcalc : P p = C + b ^ 2 - ((p : E3) 2) ^ 2 := by
        dsimp [P, C, b]; nlinarith [hsphere p]
      have hlt : P p < C ↔ 3 / 2 < f p := by
        calc
          P p < C ↔ b ^ 2 < ((p : E3) 2) ^ 2 := by
            rw [hcalc]; constructor <;> intro hh <;> linarith only [hh]
          _ ↔ b < (p : E3) 2 := sq_lt_sq₀ hbase.le hw.le
          _ ↔ 3 / 2 < f p := by
            rw [hF]; dsimp [b]; constructor <;> intro hh <;> linarith only [hh]
      have hle : P p ≤ C ↔ 3 / 2 ≤ f p := by
        calc
          P p ≤ C ↔ b ^ 2 ≤ ((p : E3) 2) ^ 2 := by
            rw [hcalc]; constructor <;> intro hh <;> linarith only [hh]
          _ ↔ b ≤ (p : E3) 2 := sq_le_sq₀ hbase.le hw.le
          _ ↔ 3 / 2 ≤ f p := by
            rw [hF]; dsimp [b]; constructor <;> intro hh <;> linarith only [hh]
      refine ⟨hlt, hle, ?_⟩; constructor
      · intro hh; have hh' := hle.mp hh.le
        have hn : ¬ 3 / 2 < f p := by intro h; have := hlt.mpr h; linarith
        linarith
      · intro hh; have hh' := hle.mpr hh.ge
        have hn : ¬ P p < C := by intro h; have := hlt.mp h; linarith
        linarith
  have hupperTarget (p : UnitTwoSphere) (hp : 3 / 2 ≤ f p) : p ∈ eP.target := by
    have hdq := (hdBounds (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2) (by positivity)).2
    have hw : 0 < (p : E3) 2 := by dsimp [f] at hp; nlinarith [sq_nonneg ((p : E3) 1)]
    have hP := (hupper p hw).2.1.mpr hp
    rw [hePt]; refine ⟨hw, ?_⟩
    apply (div_lt_iff₀ hC).2; dsimp [C] at *; nlinarith
  have hPimages : eP '' ball 0 1 = {p | 3 / 2 < f p} ∧
      eP '' closedBall 0 1 = {p | 3 / 2 ≤ f p} ∧
      eP '' sphere 0 1 = {p | f p = 3 / 2} := by
    have hvalues (x : E2) (hx : x ∈ eP.source) :
        0 < (eP x : E3) 2 ∧ P (eP x) = C * ‖x‖ ^ 2 := by
      have ht := eP.map_source hx; rw [hePt] at ht
      rw [hePs] at hx
      exact ⟨ht.1, by dsimp [P]; rw [hePf x hx]; exact hXY x⟩
    have hback (p : UnitTwoSphere) : ‖eP.symm p‖ ^ 2 = P p / C := by
      rw [hePinv]; exact hHPnorm p
    refine ⟨?_, ?_, ?_⟩ <;> ext p <;> constructor
    · rintro ⟨x, hx, rfl⟩; have hv := hvalues x (hPclosed (ball_subset_closedBall hx))
      apply (hupper _ hv.1).1.mp; rw [hv.2]
      have hn : ‖x‖ ^ 2 < 1 := by simpa only [one_pow] using (hb x 1 zero_lt_one).1 hx
      simpa only [mul_one] using mul_lt_mul_of_pos_left hn hC
    · intro hp; have ht := hupperTarget p hp.le
      have hv : 0 < (p : E3) 2 := by rw [hePt] at ht; exact ht.1
      refine ⟨eP.symm p, (hb _ 1 zero_lt_one).2 ?_, eP.right_inv ht⟩
      rw [hback]; norm_num; exact (div_lt_one hC).2 ((hupper p hv).1.mpr hp)
    · rintro ⟨x, hx, rfl⟩; have hv := hvalues x (hPclosed hx)
      apply (hupper _ hv.1).2.1.mp; rw [hv.2]; nlinarith [(hc x).1 hx]
    · intro hp; have ht := hupperTarget p hp
      have hv : 0 < (p : E3) 2 := by rw [hePt] at ht; exact ht.1
      refine ⟨eP.symm p, (hc _).2 ?_, eP.right_inv ht⟩
      rw [hback]; exact (div_le_one hC).2 ((hupper p hv).2.1.mpr hp)
    · rintro ⟨x, hx, rfl⟩; have hn := (hs x).1 hx
      have hv := hvalues x (hPclosed ((hc x).2 hn.le))
      exact (hupper _ hv.1).2.2.mp (by rw [hv.2, hn, mul_one])
    · intro hp; have ht := hupperTarget p hp.ge
      have hv : 0 < (p : E3) 2 := by rw [hePt] at ht; exact ht.1
      refine ⟨eP.symm p, (hs _).2 ?_, eP.right_inv ht⟩
      rw [hback, (hupper p hv).2.2.mpr hp]; exact div_self hC.ne'
  have curveTest (p : UnitTwoSphere) (γ : ℝ → UnitTwoSphere)
      (hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ 0) (hγ0 : γ 0 = p)
      (v : ℝ) (hv : v ≠ 0) (hder : HasDerivAt (f ∘ γ) v 0) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
    intro hz
    have hh := mfderiv_comp 0 (hf.mdifferentiable (by simp) (γ 0))
      (hγ.mdifferentiableAt (by simp))
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) 0 : ℝ →L[ℝ] ℝ) =
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ 0) : E2 →L[ℝ] ℝ).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ 0 : ℝ →L[ℝ] E2) at hh
    have hz' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ 0) = 0 := hγ0.symm ▸ hz
    rw [hz', ContinuousLinearMap.zero_comp] at hh
    have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) 0 =
        ContinuousLinearMap.toSpanSingleton ℝ v := hder.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hm] at hh
    have hv0 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hh
    apply hv
    rw [ContinuousLinearMap.toSpanSingleton_apply_one] at hv0
    exact hv0
  have hregular (p : UnitTwoSphere) (hp : f p = -1 / 8 ∨ f p = 3 / 2) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
    rcases hp with hp | hp
    · have hsign : (p : E3) 1 ≠ 0 := by
        intro hz
        have hdq := (hdBounds (((p : E3) 0) ^ 2) (sq_nonneg _)).1
        have hq : ((p : E3) 0) ^ 2 ≤ 1 := by nlinarith [hsphere p]
        by_cases hsmall : ((p : E3) 0) ^ 2 < sigma
        · dsimp [f] at hp; rw [hz] at hp; norm_num at hp
          have hw : -1 ≤ (p : E3) 2 := by nlinarith [hsphere p]
          have hsmall' : ((p : E3) 0) ^ 2 ≤ 1 / 16 := hsmall.le.trans hsigmaSmall
          have hsq := (sq_le_sq₀ (sq_nonneg ((p : E3) 0))
            (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hsmall'
          nlinarith
        · have hzq := hdZero _ (le_of_not_gt hsmall)
          dsimp [f] at hp; rw [hz] at hp; norm_num at hp
          rw [hzq] at hp; nlinarith [hsphere p]
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, 0 < eps i * (p : E3) 1 := by
        rcases lt_or_gt_of_ne hsign with h | h
        · exact ⟨1, by simpa [eps] using neg_pos.mpr h⟩
        · exact ⟨0, by simpa [eps] using h⟩
      have ht := hMtarget i p hi hp.le
      let x := (eM i).symm p
      have hx : x ∈ (eM i).source := (eM i).map_target ht
      have hxn : ‖x‖ ^ 2 = 1 := by
        have hh := hMheight i x hx; rw [(eM i).right_inv ht, hp, hR2] at hh; linarith
      let γ : ℝ → UnitTwoSphere := fun t => eM i ((1 + t) • x)
      have hγ0 : γ 0 = p := by simp [γ, x, (eM i).right_inv ht]
      have hcurve : ContDiff ℝ ∞ (fun t : ℝ => (1 + t) • x) := by fun_prop
      have hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ 0 := by
        have hchart : ContMDiffAt 𝓘(ℝ, E2) (𝓡 2) ∞ (eM i) ((1 + (0 : ℝ)) • x) := by
          simpa using (heMd i).contMDiffAt ((eM i).open_source.mem_nhds hx)
        exact hchart.comp 0 hcurve.contMDiff.contMDiffAt
      have heq : (f ∘ γ) =ᶠ[𝓝 0] fun t : ℝ => -1 / 4 + R0 ^ 2 * (1 + t) ^ 2 := by
        have hn : ∀ᶠ t : ℝ in 𝓝 0, (1 + t) • x ∈ (eM i).source :=
          hcurve.continuous.continuousAt.preimage_mem_nhds
            ((eM i).open_source.mem_nhds (by simpa using hx))
        filter_upwards [hn] with t ht'
        change f (eM i ((1 + t) • x)) = _
        rw [hMheight i _ ht', norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs, hxn, mul_one]
      apply curveTest p γ hγ hγ0 (2 * R0 ^ 2) (by positivity)
      apply HasDerivAt.congr_of_eventuallyEq _ heq
      convert! (hasDerivAt_const (0 : ℝ) (-1 / 4)).add
        (((hasDerivAt_const (0 : ℝ) 1).add (hasDerivAt_id 0)).pow 2
          |>.const_mul (R0 ^ 2)) using 1
      first | rfl | (norm_num; ring)
    · have ht := hupperTarget p hp.ge
      have hw : 0 < (p : E3) 2 := by rw [hePt] at ht; exact ht.1
      let q := ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hq : sigma < q := by
        by_contra hn
        have hqsmall : q ≤ 1 / 16 := (le_of_not_gt hn).trans hsigmaSmall
        have hw1 : (p : E3) 2 ≤ 1 := by dsimp [q] at *; nlinarith [hsphere p]
        have hwq : 1 - q ≤ (p : E3) 2 := by
          have hh := mul_nonneg hw.le (sub_nonneg.mpr hw1)
          dsimp [q] at *; nlinarith [hsphere p]
        have hq2 : q ^ 2 ≤ 1 / 256 := by nlinarith
        have hdq := (hdBounds q hq0).1
        dsimp [f] at hp; change 1 + _ - _ + d q = _ at hp
        dsimp [q] at *; nlinarith [sq_nonneg ((p : E3) 0)]
      have hqw : 1 - q = ((p : E3) 2) ^ 2 := by dsimp [q]; nlinarith [hsphere p]
      let G : ℝ → E3 := fun t => !₂[(1 + t) * (p : E3) 0,
        (1 + t) * (p : E3) 1, Real.sqrt (1 - (1 + t) ^ 2 * q)]
      have hrad : 0 < 1 - (1 + (0 : ℝ)) ^ 2 * q := by simpa [hqw] using sq_pos_of_pos hw
      have hGs : ContDiffAt ℝ ∞ G 0 := by
        apply (contDiffAt_piLp 2).2; intro j; fin_cases j
        · change ContDiffAt ℝ ∞ (fun t : ℝ => (1 + t) * (p : E3) 0) 0
          fun_prop
        · change ContDiffAt ℝ ∞ (fun t : ℝ => (1 + t) * (p : E3) 1) 0
          fun_prop
        · exact (show ContDiffAt ℝ ∞ (fun t : ℝ => 1 - (1 + t) ^ 2 * q) 0 by
            fun_prop).sqrt hrad.ne'
      have hG0 : G 0 = (p : E3) := by
        ext j; fin_cases j <;> simp [G, hqw, Real.sqrt_sq hw.le]
      let γ : ℝ → UnitTwoSphere := sphereDirection ∘ G
      have hγ0 : γ 0 = p := by
        apply Subtype.ext
        change (sphereDirection (G 0) : E3) = (p : E3)
        rw [hG0]
        exact direction _ (norm_eq_of_mem_sphere p)
      have hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ 0 :=
        (sphereDirection_contMDiffOn.contMDiffAt
          (isClosed_singleton.isOpen_compl.mem_nhds (by
            change G 0 ≠ 0; rw [hG0]; exact ne_zero_of_mem_unit_sphere p))).comp 0 hGs.contMDiffAt
      have hn : ∀ᶠ t : ℝ in 𝓝 0,
          0 < 1 - (1 + t) ^ 2 * q ∧ sigma < (1 + t) ^ 2 * q := by
        have ha : Continuous (fun t : ℝ => 1 - (1 + t) ^ 2 * q) := by fun_prop
        have hb' : Continuous (fun t : ℝ => (1 + t) ^ 2 * q) := by fun_prop
        exact (ha.continuousAt.eventually (Ioi_mem_nhds hrad)).and
          (hb'.continuousAt.eventually (Ioi_mem_nhds (by simpa using hq)))
      have heq : (f ∘ γ) =ᶠ[𝓝 0] fun t : ℝ =>
          1 + Real.sqrt (1 - (1 + t) ^ 2 * q) - (1 + t) ^ 2 * ((p : E3) 1) ^ 2 := by
        filter_upwards [hn] with t ht'
        have hunit : ‖G t‖ = 1 := by
          apply hnorm3; dsimp [G]; rw [Real.sq_sqrt ht'.1.le]; dsimp [q]; ring
        change f (sphereDirection (G t)) = _; dsimp [f]; rw [direction _ hunit]
        have hh : (G t) 0 ^ 2 + (G t) 1 ^ 2 = (1 + t) ^ 2 * q := by dsimp [G, q]; ring
        rw [hh, hdZero _ ht'.2.le]; dsimp [G]; ring
      have hder : HasDerivAt (fun t : ℝ =>
          1 + Real.sqrt (1 - (1 + t) ^ 2 * q) - (1 + t) ^ 2 * ((p : E3) 1) ^ 2)
          (-q / (p : E3) 2 - 2 * ((p : E3) 1) ^ 2) 0 := by
        have ha : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) 2 0 := by
          convert! ((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2 using 1
          first | rfl | norm_num
        have hh := ((hasDerivAt_const (0 : ℝ) 1).sub (ha.mul_const q)).sqrt hrad.ne'
        convert! ((hasDerivAt_const (0 : ℝ) 1).add hh).sub
          (ha.mul_const (((p : E3) 1) ^ 2)) using 1
        first | rfl | (norm_num only [Pi.sub_apply, add_zero, one_pow, one_mul, zero_add,
          zero_sub, hqw, Real.sqrt_sq hw.le]; field_simp [hw.ne'])
      apply curveTest p γ hγ hγ0 (-q / (p : E3) 2 - 2 * ((p : E3) 1) ^ 2) (ne_of_lt (by
        rw [neg_div]
        have hpos := div_pos (hsigma.trans hq) hw
        linarith only [hpos, sq_nonneg ((p : E3) 1)]))
      exact hder.congr_of_eventuallyEq heq
  refine ⟨eM, eP, ?_, hePs, hePt, hePd, hePi, ?_, ?_, hPclosed,
    hPimages.1, hPimages.2.1, hPimages.2.2, ?_, ?_, hregular⟩
  · intro i
    exact ⟨heMs i, heMt i, heMd i, heMi i, fun x hx => heMf i x ((heMs i) ▸ hx),
      fun p _ => heMinv i p,
      hMclosed i, hMheight i, (hMimages i).1, (hMimages i).2.1, (hMimages i).2.2⟩
  · intro x hx; exact hePf x (hePs ▸ hx)
  · intro p _; exact hePinv p
  · rw [(hMimages 0).2.1, (hMimages 1).2.1]
    apply Set.disjoint_left.2; intro p hp hq
    norm_num [eps] at hp hq; linarith [hp.1, hq.1]
  · intro i; rw [(hMimages i).2.1, hPimages.2.1]
    apply Set.disjoint_left.2
    intro p hp hq
    have hhi : 3 / 2 ≤ f p := hq
    linarith only [hp.2, hhi]

end PoincareConjecture.M25.Topology3D
