import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseMeridian
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem stackMorseProjection_geometry
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
    let U : Set E2 := {x | 0 < h x}
    let R := fun t => (stackCanonicalMeridian rFlat rOne v0 v1 t).1
    let Z := fun t => (stackCanonicalMeridian rFlat rOne v0 v1 t).2
    let w := fun t => Real.sqrt (rho ^ 2 + lambda * Z t) * R t
    ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ q ∧
      ContDiff ℝ ∞ C ∧ IsOpen U ∧ closedBall (0 : E2) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ f U ∧
      (∀ x : E2,
        -1 ≤ v x ∧ v x < 1 ∧
        heightCoordinates (q x : E3) =
          ((2 / (1 + ‖x‖ ^ 2)) • x, v x) ∧
        (C x).1 = (a (v x) * (2 / (1 + ‖x‖ ^ 2))) • x ∧
        (C x).2 = Z (v x) ∧ ‖(C x).1‖ = R (v x) ∧
        ‖f x‖ = w (v x)) ∧
      q '' closedBall (0 : E2) 1 =
        {p : UnitTwoSphere | (heightCoordinates (p : E3)).2 ≤ 0} ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        v x ∈ Icc (-1 : ℝ) 0 ∧
        rho ^ 2 - lambda ≤ h x ∧ h x ≤ rho ^ 2 ∧ ‖f x‖ ^ 2 ≤ h x) ∧
      InjOn f (closedBall (0 : E2) 1) ∧
      f '' closedBall (0 : E2) 1 = closedBall (0 : E2) rho ∧
      f 0 = 0 ∧ ∀ x ∈ sphere (0 : E2) 1, f x = rho • x := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
  let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
  let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
  let h : E2 → ℝ := fun x => rho ^ 2 + lambda * (C x).2
  let f : E2 → E2 := fun x => Real.sqrt (h x) • (C x).1
  let U : Set E2 := {x | 0 < h x}
  let R := fun t => (stackCanonicalMeridian rFlat rOne v0 v1 t).1
  let Z := fun t => (stackCanonicalMeridian rFlat rOne v0 v1 t).2
  let w := fun t => Real.sqrt (rho ^ 2 + lambda * Z t) * R t
  obtain ⟨ha, hapos, _, _, hanear, _, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨hb, _, _, _, _, _⟩ :=
    stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  obtain ⟨_, _, _, hbounds, _, hmono, himage⟩ :=
    stackMorseMeridian_geometry rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  have hD (x : E2) : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hv (x : E2) : -1 ≤ v x ∧ v x < 1 := by
    dsimp only [v]
    constructor
    · apply (le_div_iff₀ (hD x)).mpr
      nlinarith only [sq_nonneg ‖x‖]
    · apply (div_lt_iff₀ (hD x)).mpr
      linarith
  have hq (x : E2) : heightCoordinates (q x : E3) =
      ((2 / (1 + ‖x‖ ^ 2)) • x, v x) := by
    change heightCoordinates ((-northSpherePoint (-x) : UnitTwoSphere) : E3) = _
    rw [coe_neg_sphere, map_neg, northSpherePoint_coordinates, norm_neg]
    apply Prod.ext
    · change -((2 / (1 + ‖x‖ ^ 2)) • -x) = _
      rw [smul_neg, neg_neg]
    · change -((1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2)) = v x
      dsimp only [v]
      ring
  have hsqrt (x : E2) : Real.sqrt (1 - v x ^ 2) =
      2 * ‖x‖ / (1 + ‖x‖ ^ 2) := by
    have he : (2 * ‖x‖ / (1 + ‖x‖ ^ 2)) ^ 2 = 1 - v x ^ 2 := by
      dsimp only [v]
      field_simp [(hD x).ne']
      ring
    have hn : 0 ≤ 1 - v x ^ 2 := by rw [← he]; positivity
    have hp : 0 ≤ 2 * ‖x‖ / (1 + ‖x‖ ^ 2) := by positivity
    nlinarith only [Real.sq_sqrt hn, Real.sqrt_nonneg (1 - v x ^ 2), he, hp]
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos _ _ 0 le_rfl]
  have hC (x : E2) : C x =
      (a (v x) • ((2 / (1 + ‖x‖ ^ 2)) • x),
        b (a (v x) • ((2 / (1 + ‖x‖ ^ 2)) • x)) * v x) := by
    dsimp only [C]
    rw [hq, hM]
  have hC1 (x : E2) : (C x).1 =
      (a (v x) * (2 / (1 + ‖x‖ ^ 2))) • x := by
    rw [hC]
    exact smul_smul _ _ _
  have hCn (x : E2) : ‖(C x).1‖ = R (v x) := by
    rw [hC1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos (hapos _) (div_pos (by norm_num) (hD x)))]
    change a (v x) * (2 / (1 + ‖x‖ ^ 2)) * ‖x‖ =
      a (v x) * Real.sqrt (1 - v x ^ 2)
    rw [hsqrt]
    ring
  have hC2 (x : E2) : (C x).2 = Z (v x) := by
    calc
      (C x).2 = b (C x).1 * v x := by rw [hC]
      _ = Z (v x) := by
        change stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2) (‖(C x).1‖ ^ 2) * v x = _
        rw [hCn]
        rfl
  have hfn (x : E2) : ‖f x‖ = w (v x) := by
    dsimp only [f]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hCn]
    dsimp only [h]
    rw [hC2]
  have hvs : ContDiff ℝ ∞ v :=
    ((contDiff_id.norm_sq ℝ).sub contDiff_const).div
      (contDiff_const.add (contDiff_id.norm_sq ℝ)) (fun x => (hD x).ne')
  have hCs : ContDiff ℝ ∞ C := by
    have hx : ContDiff ℝ ∞
        (fun x : E2 => a (v x) • ((2 / (1 + ‖x‖ ^ 2)) • x)) :=
      (ha.comp hvs).smul
        ((contDiff_const.div (contDiff_const.add (contDiff_id.norm_sq ℝ))
          (fun x => (hD x).ne')).smul contDiff_id)
    convert hx.prodMk ((hb.comp hx).mul hvs) using 1
    exact funext hC
  have hhs : ContDiff ℝ ∞ h := contDiff_const.add (contDiff_const.mul hCs.snd)
  have hU : IsOpen U := isOpen_lt continuous_const hhs.continuous
  have hmem (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : v x ∈ Icc (-1 : ℝ) 0 := by
    refine ⟨(hv x).1, ?_⟩
    apply div_nonpos_of_nonpos_of_nonneg _ (hD x).le
    have hn := mem_closedBall_zero_iff.mp hx
    nlinarith only [hn, norm_nonneg x]
  have hbd (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      rho ^ 2 - lambda ≤ h x ∧ h x ≤ rho ^ 2 ∧ ‖f x‖ ^ 2 ≤ h x := by
    have hh := hbounds (v x) (hmem x hx)
    have he : h x = rho ^ 2 + lambda * Z (v x) := by dsimp only [h]; rw [hC2]
    rw [he, hfn]
    refine ⟨?_, ?_, hh.2.2.2.2.2.2.2⟩
    · have ht := mul_le_mul_of_nonneg_left hh.2.2.1 hlambda.le
      linarith only [ht]
    · have ht := mul_nonpos_of_nonneg_of_nonpos hlambda.le hh.2.2.2.1
      linarith only [ht]
  have hKU : closedBall (0 : E2) 1 ⊆ U := by
    intro x hx
    have ht := (hbd x hx).1
    change 0 < h x
    nlinarith only [ht, hsmall, hlambda]
  have hfs : ContDiffOn ℝ ∞ f U :=
    (hhs.contDiffOn.sqrt (fun _ hx => ne_of_gt hx)).smul hCs.fst.contDiffOn
  let k : E2 → ℝ := fun x =>
    Real.sqrt (h x) * a (v x) * (2 / (1 + ‖x‖ ^ 2))
  have hfk (x : E2) : f x = k x • x := by
    dsimp only [f, k]
    rw [hC1, smul_smul]
    congr 1
    ring
  have hk (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : 0 < k x :=
    mul_pos (mul_pos (Real.sqrt_pos.mpr (hKU hx)) (hapos _))
      (div_pos (by norm_num) (hD x))
  have hzero : f 0 = 0 := by rw [hfk, smul_zero]
  have hinj : InjOn f (closedBall (0 : E2) 1) := by
    intro x hx y hy hxy
    have hn := congrArg norm hxy
    rw [hfn, hfn] at hn
    have he := hmono.injOn (hmem x hx) (hmem y hy) hn
    have hs : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
      have ht := (div_eq_div_iff (hD x).ne' (hD y).ne').mp he
      nlinarith only [ht]
    have hh : h x = h y := by
      dsimp only [h]
      rw [hC2, hC2, he]
    have hke : k x = k y := by dsimp only [k]; rw [hh, he, hs]
    have ht := congrArg (fun z : E2 => (k x)⁻¹ • z) hxy
    rw [hfk, hfk, ← hke, smul_smul, smul_smul,
      inv_mul_cancel₀ (hk x hx).ne', one_smul, one_smul] at ht
    exact ht
  have hfi : f '' closedBall (0 : E2) 1 = closedBall (0 : E2) rho := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply mem_closedBall_zero_iff.mpr
      rw [hfn]
      exact (hbounds (v x) (hmem x hx)).2.2.2.2.2.2.1
    · intro hy
      by_cases hy0 : y = 0
      · subst y
        exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), hzero⟩
      have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hwy : ‖y‖ ∈ w '' Icc (-1 : ℝ) 0 := by
        rw [himage]
        exact ⟨hny.le, mem_closedBall_zero_iff.mp hy⟩
      obtain ⟨t, ht, hwt⟩ := hwy
      have htlo : -1 < t := by
        apply lt_of_le_of_ne ht.1
        intro he
        have hw0 : w (-1) = 0 := by
          simp only [w, R, stackCanonicalMeridian]
          norm_num
        rw [← he, hw0] at hwt
        exact hny.ne' hwt.symm
      have hden : 0 < 1 - t := by linarith only [ht.2]
      have hnum : 0 < 1 + t := by linarith only [htlo]
      let r := Real.sqrt ((1 + t) / (1 - t))
      have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hnum hden)
      have hr2 : r ^ 2 = (1 + t) / (1 - t) := Real.sq_sqrt (div_pos hnum hden).le
      have hreq : r ^ 2 * (1 - t) = 1 + t := (eq_div_iff hden.ne').mp hr2
      have hrle : r ≤ 1 := by
        have he : r ^ 2 ≤ 1 := by
          rw [hr2]
          apply (div_le_one hden).mpr
          linarith only [ht.2]
        nlinarith only [he, hr]
      let x : E2 := (r / ‖y‖) • y
      have hxn : ‖x‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hny)]
        exact div_mul_cancel₀ r hny.ne'
      have hx : x ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr (hxn.le.trans hrle)
      have hvt : v x = t := by
        dsimp only [v]
        rw [hxn]
        apply (div_eq_iff (show 1 + r ^ 2 ≠ 0 by positivity)).mpr
        nlinarith only [hreq]
      have hkr : k x * r = ‖y‖ := by
        have hn := hfn x
        rw [hfk, norm_smul, Real.norm_eq_abs, abs_of_pos (hk x hx), hxn, hvt, hwt] at hn
        exact hn
      refine ⟨x, hx, ?_⟩
      rw [hfk]
      change k x • ((r / ‖y‖) • y) = y
      rw [smul_smul, ← mul_div_assoc, hkr, div_self hny.ne', one_smul]
  have hqi : q '' closedBall (0 : E2) 1 =
      {p : UnitTwoSphere | (heightCoordinates (p : E3)).2 ≤ 0} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (heightCoordinates (q x : E3)).2 ≤ 0
      rw [hq]
      exact (hmem x hx).2
    · intro hp
      have hn : -p ∈ northSpherePoint '' closedBall (0 : E2) 1 := by
        rw [northSpherePoint_image_closedBall]
        change 0 ≤ (heightCoordinates ((-p : UnitTwoSphere) : E3)).2
        rw [coe_neg_sphere, map_neg]
        exact neg_nonneg.mpr hp
      obtain ⟨x, hx, he⟩ := hn
      refine ⟨-x, ?_, ?_⟩
      · simpa only [mem_closedBall_zero_iff, norm_neg] using hx
      · dsimp only [q]
        rw [neg_neg, he, neg_neg]
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hqs : ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ q :=
    contMDiff_neg_sphere.comp (northSpherePoint_contMDiff.comp contDiff_neg.contMDiff)
  refine ⟨hqs, hCs, hU, hKU, hfs,
    fun x => ⟨(hv x).1, (hv x).2, hq x, hC1 x, hC2 x, hCn x, hfn x⟩,
    hqi, fun x hx => ⟨hmem x hx, hbd x hx⟩, hinj, hfi, hzero, ?_⟩
  intro x hx
  have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hvx : v x = 0 := by dsimp only [v]; rw [hxn]; norm_num
  have ha0 : a 0 = 1 := by
    have ht := hanear 0 (by simpa only [abs_zero] using hv0.le)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_one, inv_one] using ht
  have hcx : (C x).1 = x := by rw [hC1, hvx, ha0, hxn]; norm_num
  have hch : (C x).2 = 0 := by rw [hC2, hvx]; simp only [Z, stackCanonicalMeridian, mul_zero]
  dsimp only [f, h]
  rw [hcx, hch, mul_zero, add_zero, Real.sqrt_sq hrho.le]

end PoincareConjecture.M25.Topology3D
