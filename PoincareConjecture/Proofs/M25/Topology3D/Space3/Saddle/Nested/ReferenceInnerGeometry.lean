import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem inner_reference_convex_geometry :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let Q : Set E2 := Metric.closedBall 0 (1 / 2)
    ContDiffOn ℝ ∞ U (Metric.ball 0 1) ∧
    StrictConvexOn ℝ Q U ∧
    (∀ v ∈ Q, ∀ w : E2, w ≠ 0 →
      ‖w‖ ^ 2 / 3 < (fderiv ℝ (fderiv ℝ U) v w) w) ∧
    (∀ v ∈ Q, (63 : ℝ) / 64 ≤ U v) ∧
    (∀ v ∈ Metric.sphere (0 : E2) (1 / 2), (69 : ℝ) / 64 < U v) ∧
    (∀ x ∈ Q, ∀ y ∈ Q,
      U x + fderiv ℝ U x (y - x) + ‖y - x‖ ^ 2 / 6 ≤ U y) ∧
    ∃ vmin ∈ Metric.ball (0 : E2) (1 / 2),
      (63 : ℝ) / 64 ≤ U vmin ∧ U vmin ≤ 1 ∧
      fderiv ℝ U vmin = 0 ∧
      (∀ v ∈ Q, fderiv ℝ U v = 0 ↔ v = vmin) ∧
      Function.Injective (fderiv ℝ (fderiv ℝ U) vmin) ∧
      (∀ v ∈ Q, U vmin + ‖v - vmin‖ ^ 2 / 6 ≤ U v) ∧
      (∀ b : ℝ, b ≤ (17 : ℝ) / 16 + 2 / 8192 →
        IsCompact {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
        {v : E2 | v ∈ Q ∧ U v ≤ b} ⊆ Metric.ball 0 (1 / 2)) := by
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let Q : Set E2 := closedBall 0 (1 / 2)
  let s : E2 → ℝ := fun v => Real.sqrt (1 - ‖v‖ ^ 2)
  let A : E2 → ℝ := fun v => 2 - 1 / s v
  let P : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let I : E2 →L[ℝ] E2 →L[ℝ] ℝ := (innerSL ℝ (E := E2)).toContinuousLinearMap
  change ContDiffOn ℝ ∞ U (ball 0 1) ∧ _
  have hrad (v : E2) (hv : v ∈ ball (0 : E2) 1) : 0 < 1 - ‖v‖ ^ 2 := by
    rw [mem_ball_zero_iff] at hv
    nlinarith only [norm_nonneg v, hv]
  have hspos (v : E2) (hv : v ∈ ball (0 : E2) 1) : 0 < s v :=
    Real.sqrt_pos.mpr (hrad v hv)
  have hQunit : Q ⊆ ball (0 : E2) 1 := by
    intro v hv
    rw [mem_ball_zero_iff]
    have hn : ‖v‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hv
    linarith only [hn]
  have hcont : Continuous U :=
    ((continuous_norm.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))).add
      (P.continuous.div_const 32)
  have hsmooth : ContDiffOn ℝ ∞ U (ball (0 : E2) 1) := by
    exact ((contDiff_norm_sq ℝ).contDiffOn.add
      ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn.sqrt
        (fun v hv => (hrad v hv).ne'))).add (P.contDiff.div_const 32).contDiffOn
  have hfirst (v : E2) (hv : v ∈ ball (0 : E2) 1) :
      HasFDerivAt U (A v • innerSL ℝ v + (1 / 32 : ℝ) • P) v := by
    have hsq := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
    have hs := (hsq.const_sub (1 : ℝ)).sqrt (hrad v hv).ne'
    have hp := (P.hasFDerivAt (x := v)).const_smul (1 / 32 : ℝ)
    have hh := (hsq.add hs).add hp
    convert! hh using 1
    · ext y
      change _ = ‖y‖ ^ 2 + s y + (1 / 32 : ℝ) * y 0
      dsimp only [U, s]
      ring
    · ext w
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, innerSL_apply_apply]
      dsimp only [A, s]
      field_simp [(hspos v hv).ne']
      ring
  have hsecond (v : E2) (hv : v ∈ ball (0 : E2) 1) :
      HasFDerivAt (fderiv ℝ U)
        (A v • I +
          ((-(1 / (s v) ^ 3)) • innerSL ℝ v).smulRight (innerSL ℝ v)) v := by
    have hscalar : HasDerivAt (fun r : ℝ => 2 - 1 / Real.sqrt (1 - r))
        (-1 / (2 * (s v) ^ 3)) (‖v‖ ^ 2) := by
      have hh := ((((hasDerivAt_id (‖v‖ ^ 2)).const_sub (1 : ℝ)).sqrt
        (hrad v hv).ne').inv (hspos v hv).ne').const_sub (2 : ℝ)
      convert! hh using 1
      · ext r
        simp only [one_div, Pi.inv_apply, id_eq]
      · dsimp only [s, id_eq]
        field_simp [(hspos v hv).ne']
    have ha : HasFDerivAt A (-(1 / (s v) ^ 3) • innerSL ℝ v) v := by
      convert! hscalar.comp_hasFDerivAt v
        (hasStrictFDerivAt_norm_sq v).hasFDerivAt using 1
      ext w
      simp only [smul_apply, smul_eq_mul,
        innerSL_apply_apply]
      ring
    have hj := (ha.smul I.hasFDerivAt).add_const
        ((1 / 32 : ℝ) • P)
    apply hj.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hv] with y hy
    exact (hfirst y hy).fderiv
  have hdiag (v : E2) (hv : v ∈ ball (0 : E2) 1) (w : E2) :
      (fderiv ℝ (fderiv ℝ U) v w) w =
        (2 - 1 / s v) * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 / (s v) ^ 3 := by
    rw [(hsecond v hv).fderiv]
    change (A v * ⟪w, w⟫_ℝ + (-(1 / (s v) ^ 3) * ⟪v, w⟫_ℝ) * ⟪v, w⟫_ℝ) = _
    rw [real_inner_self_eq_norm_sq]
    dsimp only [A]
    ring
  have hpositive (v : E2) (hv : v ∈ Q) (w : E2) (hw : w ≠ 0) :
      ‖w‖ ^ 2 / 3 < (fderiv ℝ (fderiv ℝ U) v w) w := by
    have hn : ‖v‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hv
    have hp := hspos v (hQunit hv)
    have he : (s v) ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt (hrad v (hQunit hv)).le
    have hs2 : (3 : ℝ) / 4 ≤ (s v) ^ 2 := by
      nlinarith only [he, hn, norm_nonneg v]
    have hs : (4 : ℝ) / 5 < s v := by nlinarith only [hs2, hp]
    have hc : (3 : ℝ) / 5 < (s v) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right hs2 hp.le
      nlinarith only [hm, hs]
    have hcs : ⟪v, w⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
      simpa only [pow_two, real_inner_self_eq_norm_sq] using
        real_inner_mul_inner_self_le v w
    have hw2 : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw) 2
    have hm := mul_pos (show 0 < (s v) ^ 3 - 3 / 5 by linarith only [hc]) hw2
    have hew := congrArg (fun z : ℝ => z * ‖w‖ ^ 2) he
    rw [hdiag v (hQunit hv) w]
    apply (mul_lt_mul_iff_left₀ (pow_pos hp 3)).mp
    have halg : ((2 - 1 / s v) * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 / (s v) ^ 3) *
        (s v) ^ 3 = (2 * (s v) ^ 3 - (s v) ^ 2) * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 := by
      field_simp [hp.ne']
    rw [halg]
    nlinarith only [hcs, hm, hew]
  have hbound (v : E2) (hv : v ∈ Q) : (63 : ℝ) / 64 ≤ U v := by
    have hn : ‖v‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hv
    have hcoord : |v 0| ≤ ‖v‖ := PiLp.norm_apply_le v 0
    have hs0 := (hspos v (hQunit hv)).le
    have hs2 : (s v) ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt (hrad v (hQunit hv)).le
    have hs1 : s v ≤ 1 := by nlinarith only [hs0, hs2, sq_nonneg ‖v‖]
    have hprod := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    have hcoord' := (abs_le.mp hcoord).1
    change _ ≤ ‖v‖ ^ 2 + s v + v 0 / 32
    nlinarith only [hs2, hprod, hcoord', hn]
  have hboundary (v : E2) (hv : v ∈ sphere (0 : E2) (1 / 2)) :
      (69 : ℝ) / 64 < U v := by
    have hn : ‖v‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp hv
    have hcoord : |v 0| ≤ 1 / 2 := hn ▸ PiLp.norm_apply_le v 0
    have hs0 := Real.sqrt_nonneg (1 - ‖v‖ ^ 2)
    have hs2 : (s v) ^ 2 = 3 / 4 := by
      dsimp only [s]
      rw [Real.sq_sqrt (by rw [hn]; norm_num), hn]
      norm_num
    have hs : (27 : ℝ) / 32 < s v := by nlinarith only [hs0, hs2]
    have hcoord' := (abs_le.mp hcoord).1
    change _ < ‖v‖ ^ 2 + s v + v 0 / 32
    rw [hn]
    nlinarith only [hs, hcoord']
  have hconv : Convex ℝ Q := convex_closedBall _ _
  have htangent (x : E2) (hx : x ∈ Q) (y : E2) (hy : y ∈ Q) :
      U x + fderiv ℝ U x (y - x) + ‖y - x‖ ^ 2 / 6 ≤ U y := by
    let w := y - x
    let p : ℝ → E2 := fun t => x + t • w
    let g : ℝ → ℝ := fun t => U (p t) - ‖w‖ ^ 2 * t ^ 2 / 6
    let gp : ℝ → ℝ := fun t => fderiv ℝ U (p t) w - ‖w‖ ^ 2 * t / 3
    have hpQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ Q := by
      have hh := hconv hx hy (show 0 ≤ 1 - t by linarith [ht.2]) ht.1
        (show 1 - t + t = 1 by ring)
      convert! hh using 1
      dsimp only [p, w]
      module
    have hp (t : ℝ) : HasDerivAt p w t := by
      simpa only [one_smul, id_eq, p] using ((hasDerivAt_id t).smul_const w).const_add x
    have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (gp t) t := by
      have hh := ((hfirst (p t) (hQunit (hpQ t ht))).comp_hasDerivAt t (hp t)).sub
        ((((hasDerivAt_id t).pow 2).const_mul (‖w‖ ^ 2)).div_const 6)
      convert! hh using 1
      dsimp only [gp]
      rw [(hfirst (p t) (hQunit (hpQ t ht))).fderiv]
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
      ring
    have hgp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt gp
        ((fderiv ℝ (fderiv ℝ U) (p t) w) w - ‖w‖ ^ 2 / 3) t := by
      have hh := (((hsecond (p t) (hQunit (hpQ t ht))).comp_hasDerivAt t
        (hp t)).clm_apply (hasDerivAt_const t w)).sub
          (((hasDerivAt_id t).const_mul (‖w‖ ^ 2)).div_const 3)
      convert! hh using 1
      rw [(hsecond (p t) (hQunit (hpQ t ht))).fderiv]
      simp only [ContinuousLinearMap.map_zero, add_zero, mul_one]
    have hmono : MonotoneOn gp (Icc (0 : ℝ) 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (hgp t ht).continuousAt.continuousWithinAt)
        (fun t ht => (hgp t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [(hgp t (interior_subset ht)).deriv]
      by_cases hw : w = 0
      · simp only [hw, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
          ContinuousLinearMap.map_zero, sub_zero, le_refl]
      · exact sub_nonneg.mpr (hpositive (p t) (hpQ t (interior_subset ht)) w hw).le
    have hmean := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (C := gp 0) (fun t ht => by
        rw [(hg t (interior_subset ht)).deriv]
        exact hmono (by norm_num) (interior_subset ht) (interior_subset ht).1)
      0 (by norm_num) 1 (by norm_num) (by norm_num)
    have hp0 : p 0 = x := by simp only [p, zero_smul, add_zero]
    have hp1 : p 1 = y := by simp only [p, w, one_smul, add_sub_cancel]
    dsimp only [g, gp] at hmean
    rw [hp0, hp1] at hmean
    dsimp only [w] at hmean
    nlinarith only [hmean]
  have hstrict : StrictConvexOn ℝ Q U := by
    refine ⟨hconv, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    let z := a • x + b • y
    have hz : z ∈ Q := hconv hx hy ha.le hb.le hab
    have hxz : x - z ≠ 0 := by
      have he : x - z = b • (x - y) := by
        dsimp only [z]
        have : a = 1 - b := by linarith only [hab]
        rw [this]
        module
      rw [he]
      exact smul_ne_zero hb.ne' (sub_ne_zero.mpr hxy)
    have hxx := htangent z hz x hx
    have hyy := htangent z hz y hy
    have hhx : U z + fderiv ℝ U z (x - z) < U x := by
      have hp := pow_pos (norm_pos_iff.mpr hxz) 2
      linarith only [hxx, hp]
    have hhy : U z + fderiv ℝ U z (y - z) ≤ U y := by
      linarith only [hyy, sq_nonneg ‖y - z‖]
    have hd : a * fderiv ℝ U z (x - z) + b * fderiv ℝ U z (y - z) = 0 := by
      calc
        _ = fderiv ℝ U z (a • (x - z) + b • (y - z)) := by
          simp only [map_add, map_smul, smul_eq_mul]
        _ = 0 := by
          have he : a • (x - z) + b • (y - z) = 0 := by
            dsimp only [z]
            have : a = 1 - b := by linarith only [hab]
            rw [this]
            module
          rw [he, map_zero]
    have hm1 := mul_lt_mul_of_pos_left hhx ha
    have hm2 := mul_le_mul_of_nonneg_left hhy hb.le
    change U z < a * U x + b * U y
    nlinarith only [hm1, hm2, hd, congrArg (fun t : ℝ => t * U z) hab]
  have hzero : (0 : E2) ∈ Q := by simp only [Q, mem_closedBall_zero_iff, norm_zero]; norm_num
  obtain ⟨vmin, hvmin, hmin⟩ := (isCompact_closedBall (0 : E2) (1 / 2)).exists_isMinOn
    ⟨0, hzero⟩ hcont.continuousOn
  have hminone : U vmin ≤ 1 := by
    have he : U 0 = 1 := by norm_num [U]
    exact he ▸ (show U vmin ≤ U 0 from hmin hzero)
  have hminball : vmin ∈ ball (0 : E2) (1 / 2) := by
    rw [mem_ball_zero_iff]
    have hn : ‖vmin‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hvmin
    rcases lt_or_eq_of_le hn with hn | hn
    · exact hn
    · have hb := hboundary vmin (mem_sphere_zero_iff_norm.mpr hn)
      linarith only [hb, hminone]
  have hcritical : fderiv ℝ U vmin = 0 :=
    (hmin.isLocalMin (mem_of_superset (isOpen_ball.mem_nhds hminball)
      ball_subset_closedBall)).fderiv_eq_zero
  have hgap (v : E2) (hv : v ∈ Q) : U vmin + ‖v - vmin‖ ^ 2 / 6 ≤ U v := by
    simpa only [hcritical, zero_apply, add_zero] using
      htangent vmin hvmin v hv
  refine ⟨hsmooth, hstrict, hpositive, hbound, hboundary, htangent,
    vmin, hminball, hbound vmin hvmin, hminone, hcritical, ?_, ?_, hgap, ?_⟩
  · intro v hv
    constructor
    · intro hc
      have h1 := htangent v hv vmin hvmin
      have h2 := hgap v hv
      rw [hc, zero_apply, add_zero] at h1
      have he : ‖v - vmin‖ = 0 := by
        nlinarith only [h1, h2, sq_nonneg ‖vmin - v‖, sq_nonneg ‖v - vmin‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp he)
    · rintro rfl
      exact hcritical
  · intro x y hxy
    by_contra hn
    have hh := hpositive vmin hvmin (x - y) (sub_ne_zero.mpr hn)
    have he : fderiv ℝ (fderiv ℝ U) vmin (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [he, zero_apply] at hh
    have hp := sq_nonneg ‖x - y‖
    linarith only [hh, hp]
  · intro b hb
    refine ⟨(isCompact_closedBall (0 : E2) (1 / 2)).inter_right
      (isClosed_le hcont continuous_const), ?_⟩
    intro v hv
    change v ∈ Q ∧ U v ≤ b at hv
    rw [mem_ball_zero_iff]
    have hn : ‖v‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hv.1
    rcases lt_or_eq_of_le hn with hn | hn
    · exact hn
    · have hh := hboundary v (mem_sphere_zero_iff_norm.mpr hn)
      linarith only [hh, hv.2, hb]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
