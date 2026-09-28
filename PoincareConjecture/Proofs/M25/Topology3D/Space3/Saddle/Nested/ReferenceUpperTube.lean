import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceUpperLocalFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

open Set Metric
open scoped ContDiff Pointwise

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_upper_reference_tube :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let L : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let C : E3 ≃L[ℝ] (E2 × ℝ) := heightCoordinates
    ∃ ws wm : ℝ,
      1 / 2 < ws ∧ ws < 3 / 4 ∧ g ws = 1 / 32 ∧
      0 < wm ∧ wm < 1 / 2 ∧ g wm = -(1 / 32) ∧
      let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
      let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
      let k : ℝ := U vs
      let mu : ℝ := U vm
      ∃ (rho : ℝ) (e0 e : OpenPartialHomeomorph E2 E2) (c : ℝ → ℝ),
        ‖vs‖ < 1 ∧ ‖vm‖ < 1 ∧
        (37 : ℝ) / 32 < k ∧ k < 5 / 4 ∧ 5 / 4 < mu ∧
        (∀ v ∈ Metric.closedBall (0 : E2) 1, U v ≤ mu) ∧
        (∀ v ∈ Metric.closedBall (0 : E2) 1, U v = mu ↔ v = vm) ∧
        0 < rho ∧ k < mu - 9 * rho ^ 2 ∧
        e0 0 = vm ∧ Metric.closedBall 0 (4 * rho) ⊆ e0.source ∧
        e0.target ⊆ Metric.ball 0 1 ∧
        ContDiffOn ℝ ∞ e0 e0.source ∧
        ContDiffOn ℝ ∞ e0.symm e0.target ∧
        (∀ p ∈ e0.source, U (e0 p) = mu - ‖p‖ ^ 2) ∧
        (∀ v ∈ Metric.closedBall (0 : E2) 1,
          mu - 9 * rho ^ 2 ≤ U v →
            v ∈ e0.target ∧ ‖e0.symm v‖ ≤ 3 * rho) ∧
        (∀ p ∈ Metric.closedBall (0 : E2) (3 * rho),
          L (e0 p) < mu - 9 * rho ^ 2) ∧
        e = e0.restrOpen (Metric.ball 0 (3 * rho)) isOpen_ball ∧
        e.source = Metric.ball 0 (3 * rho) ∧
        e.target = e0 '' Metric.ball 0 (3 * rho) ∧
        (∀ p : E2, e p = e0 p) ∧
        (∀ v : E2, e.symm v = e0.symm v) ∧
        ContDiffOn ℝ ∞ e e.source ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        (∀ p ∈ e.source, U (e p) = mu - ‖p‖ ^ 2) ∧
        let nu : ℝ := mu - rho ^ 2
        let delta : ℝ := rho ^ 2 / 8
        ContDiff ℝ ∞ c ∧
        (∀ z : ℝ, c z ∈ Icc (nu - 3 * delta / 4) (nu + 3 * delta / 4)) ∧
        EqOn c id (Icc (nu - delta / 2) (nu + delta / 2)) ∧
        (∀ d : ℝ,
          let S : Set E3 := (nestedReferenceBallChart d).boundary
          (∀ y ∈ S, mu - 9 * rho ^ 2 + d ≤ H0 y →
            let v : E2 := (heightCoordinates y).1
            v ∈ e0.target ∧ ‖e0.symm v‖ ≤ 3 * rho ∧
            y = heightCoordinates.symm (v, U v + d)) ∧
          ∀ h ∈ Set.Icc (nu - delta / 4) (nu + delta / 4),
            0 < mu - h ∧ mu - h < 2 * rho ^ 2 ∧
            Metric.closedBall (0 : E2) (Real.sqrt (mu - h)) ⊆ e.source ∧
            S ∩ {y : E3 | h + d ≤ H0 y} ⊆
              {y : E3 | (heightCoordinates y).1 ∈ e.target} ∧
            S ∩ {y : E3 | h + d ≤ H0 y} =
              (fun p : E2 => heightCoordinates.symm (e p, U (e p) + d)) ''
                Metric.closedBall (0 : E2) (Real.sqrt (mu - h))) ∧
        ∀ d : ℝ,
          let r : ℝ → ℝ := fun z => Real.sqrt (mu - c (z - d))
          ∃ T : OpenPartialHomeomorph (E2 × ℝ) E3,
            ContDiff ℝ ∞ r ∧
            (∀ z : ℝ, 0 < r z ∧ (r z) ^ 2 < 2 * rho ^ 2 ∧ r z < 3 * rho) ∧
            (∀ p : E2 × ℝ, T p = C.symm (e (r p.2 • p.1), p.2)) ∧
            (∀ y : E3, T.symm y =
              ((r (C y).2)⁻¹ • e.symm (C y).1, (C y).2)) ∧
            T.source = {p : E2 × ℝ | r p.2 • p.1 ∈ e.source} ∧
            T.target = {y : E3 | (C y).1 ∈ e.target} ∧
            ContDiffOn ℝ ∞ T T.source ∧
            ContDiffOn ℝ ∞ T.symm T.target ∧
            Metric.closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
            (∀ p : E2 × ℝ, (C (T p)).2 = p.2) ∧
            (∀ y : E3, (T.symm y).2 = (C y).2) ∧
            ∀ z : ℝ, z - d ∈ Icc (nu - delta / 2) (nu + delta / 2) →
              T '' (Metric.closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                C.symm '' ({v : E2 | v ∈ e.target ∧ z - d ≤ U v} ×ˢ
                  ({z} : Set ℝ)) ∧
              T '' (Metric.ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                C.symm '' ({v : E2 | v ∈ e.target ∧ z - d < U v} ×ˢ
                  ({z} : Set ℝ)) ∧
              T '' (Metric.sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                C.symm '' ({v : E2 | v ∈ e.target ∧ U v = z - d} ×ˢ
                  ({z} : Set ℝ)) ∧
              T '' (Metric.sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                (nestedReferenceBallChart d).boundary ∩ {y : E3 | H0 y = z} := by
  classical
  dsimp only
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let C := heightCoordinates
  obtain ⟨ws, wm, hwslo, hwsup, hwsroot, hwmp, hwmh, hwmroot,
    rho, e0, e, hvs, hvm, hklo, hkhi, hmulo, hmax, hunique, hrho,
    hsep, hzero, hbuffer, htargetD, he0, he0i, hquad0, hfull,
    hlower, hrestrict, hsource, htarget, hefun, heinv, he, hei, hquad, hwhole⟩ :=
      exists_upper_reference_local_filling
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  let mu := U vm
  let nu := mu - rho ^ 2
  let delta := rho ^ 2 / 8
  change ∀ p ∈ e0.source, U (e0 p) = mu - ‖p‖ ^ 2 at hquad0
  change ∀ p ∈ e.source, U (e p) = mu - ‖p‖ ^ 2 at hquad
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hdelta : 0 < delta := div_pos hrho2 (by norm_num)
  obtain ⟨c, hc, hcrange, hcid⟩ := exists_saddle_end_height_clamp
    (nu - delta / 2) (nu + delta / 2) (delta / 4)
      (by linarith only [hdelta]) (by positivity)
  have hcr (z : ℝ) : c z ∈ Icc (nu - 3 * delta / 4) (nu + 3 * delta / 4) := by
    have hh := hcrange z
    constructor <;> linarith only [hh.1, hh.2]
  refine ⟨ws, wm, hwslo, hwsup, hwsroot, hwmp, hwmh, hwmroot,
    rho, e0, e, c, hvs, hvm, hklo, hkhi, hmulo, hmax, hunique, hrho,
    hsep, hzero, hbuffer, htargetD, he0, he0i, hquad0, hfull,
    hlower, hrestrict, hsource, htarget, hefun, heinv, he, hei, hquad,
    hc, hcr, hcid, hwhole, ?_⟩
  intro d
  let r : ℝ → ℝ := fun z => Real.sqrt (mu - c (z - d))
  have harg (z : ℝ) : 0 < mu - c (z - d) ∧ mu - c (z - d) < 2 * rho ^ 2 := by
    have hh := hcr (z - d)
    dsimp only [nu, delta] at hh
    constructor <;> nlinarith only [hh.1, hh.2, hrho2]
  have hr : ContDiff ℝ ∞ r :=
    (contDiff_const.sub (hc.comp (contDiff_id.sub contDiff_const))).sqrt
      (fun z => (harg z).1.ne')
  have hrb (z : ℝ) : 0 < r z ∧ (r z) ^ 2 < 2 * rho ^ 2 ∧ r z < 3 * rho := by
    have hp : 0 < r z := Real.sqrt_pos.mpr (harg z).1
    have hs : (r z) ^ 2 = mu - c (z - d) := Real.sq_sqrt (harg z).1.le
    refine ⟨hp, by rw [hs]; exact (harg z).2, ?_⟩
    nlinarith only [hp, hs, (harg z).2, hrho, hrho2]
  have hri : ContDiff ℝ ∞ (fun z => (r z)⁻¹) := hr.inv (fun z => (hrb z).1.ne')
  let S : Set (E2 × ℝ) := {p | r p.2 • p.1 ∈ e.source}
  let V : Set E3 := {y | (C y).1 ∈ e.target}
  let f : E2 × ℝ → E3 := fun p => C.symm (e (r p.2 • p.1), p.2)
  let g : E3 → E2 × ℝ := fun y => ((r (C y).2)⁻¹ • e.symm (C y).1, (C y).2)
  have ha : ContDiff ℝ ∞ (fun p : E2 × ℝ => r p.2 • p.1) :=
    (hr.comp contDiff_snd).smul contDiff_fst
  have hS : IsOpen S := e.open_source.preimage ha.continuous
  have hV : IsOpen V := e.open_target.preimage C.continuous.fst
  have hf : ContDiffOn ℝ ∞ f S := C.symm.contDiff.comp_contDiffOn
    ((he.comp ha.contDiffOn (fun _ hp => hp)).prodMk contDiff_snd.contDiffOn)
  have hg : ContDiffOn ℝ ∞ g V :=
    (((hri.comp C.contDiff.snd).contDiffOn).smul
      (hei.comp C.contDiff.fst.contDiffOn (fun _ hy => hy))).prodMk
        C.contDiff.snd.contDiffOn
  have hmapf (p : E2 × ℝ) (hp : p ∈ S) : f p ∈ V := by
    change (C (C.symm (e (r p.2 • p.1), p.2))).1 ∈ e.target
    rw [C.apply_symm_apply]
    exact e.map_source hp
  have hmapg (y : E3) (hy : y ∈ V) : g y ∈ S := by
    change r (C y).2 • ((r (C y).2)⁻¹ • e.symm (C y).1) ∈ e.source
    rw [smul_smul, mul_inv_cancel₀ (hrb _).1.ne', one_smul]
    exact e.map_target hy
  have hgf (p : E2 × ℝ) (hp : p ∈ S) : g (f p) = p := by
    dsimp only [g, f]
    rw [C.apply_symm_apply, e.left_inv hp, smul_smul,
      inv_mul_cancel₀ (hrb _).1.ne', one_smul]
  have hfg (y : E3) (hy : y ∈ V) : f (g y) = y := by
    dsimp only [f, g]
    rw [smul_smul, mul_inv_cancel₀ (hrb _).1.ne', one_smul,
      e.right_inv hy, Prod.eta, C.symm_apply_apply]
  let T : OpenPartialHomeomorph (E2 × ℝ) E3 :=
    { toFun := f
      invFun := g
      source := S
      target := V
      map_source' := hmapf
      map_target' := hmapg
      left_inv' := hgf
      right_inv' := hfg
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg.continuousOn
      open_source := hS
      open_target := hV }
  have hclosed : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source := by
    rintro ⟨x, z⟩ ⟨hx, _hz⟩
    change r z • x ∈ e.source
    rw [hsource, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hrb z).1]
    exact (mul_le_of_le_one_right (hrb z).1.le (mem_closedBall_zero_iff.mp hx)).trans_lt
      (hrb z).2.2
  have hheight (p : E2 × ℝ) : (C (T p)).2 = p.2 := by
    change (C (C.symm (e (r p.2 • p.1), p.2))).2 = p.2
    rw [C.apply_symm_apply]
  refine ⟨T, hr, hrb, fun _ => rfl, fun _ => rfl, rfl, rfl, hf, hg,
    hclosed, hheight, fun _ => rfl, ?_⟩
  intro z hz
  change z - d ∈ Icc (nu - delta / 2) (nu + delta / 2) at hz
  have hrz : (r z) ^ 2 = mu - (z - d) := by
    change (Real.sqrt (mu - c (z - d))) ^ 2 = _
    rw [Real.sq_sqrt (harg z).1.le, hcid hz]
    rfl
  have hsrc : closedBall (0 : E2) (r z) ⊆ e.source := by
    intro p hp
    rw [hsource, mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hp).trans_lt (hrb z).2.2
  have hqi (v : E2) (hv : v ∈ e.target) : ‖e.symm v‖ ^ 2 = mu - U v := by
    have hh := hquad (e.symm v) (e.map_target hv)
    rw [e.right_inv hv] at hh
    linarith only [hh]
  have hslices :
      e '' closedBall 0 (r z) = {v : E2 | v ∈ e.target ∧ z - d ≤ U v} ∧
      e '' ball 0 (r z) = {v : E2 | v ∈ e.target ∧ z - d < U v} ∧
      e '' sphere 0 (r z) = {v : E2 | v ∈ e.target ∧ U v = z - d} := by
    refine ⟨?_, ?_, ?_⟩
    · ext v
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hn := mem_closedBall_zero_iff.mp hp
        refine ⟨e.map_source (hsrc hp), ?_⟩
        rw [hquad p (hsrc hp)]
        nlinarith only [hn, norm_nonneg p, (hrb z).1, hrz]
      · rintro ⟨hv, hh⟩
        refine ⟨e.symm v, mem_closedBall_zero_iff.mpr ?_, e.right_inv hv⟩
        nlinarith only [hqi v hv, hh, norm_nonneg (e.symm v), (hrb z).1, hrz]
    · ext v
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hpS := hsrc (ball_subset_closedBall hp)
        have hn := mem_ball_zero_iff.mp hp
        refine ⟨e.map_source hpS, ?_⟩
        rw [hquad p hpS]
        nlinarith only [hn, norm_nonneg p, (hrb z).1, hrz]
      · rintro ⟨hv, hh⟩
        refine ⟨e.symm v, mem_ball_zero_iff.mpr ?_, e.right_inv hv⟩
        nlinarith only [hqi v hv, hh, norm_nonneg (e.symm v), (hrb z).1, hrz]
    · ext v
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hn := mem_sphere_zero_iff_norm.mp hp
        have hpS := hsrc (mem_closedBall_zero_iff.mpr hn.le)
        refine ⟨e.map_source hpS, ?_⟩
        rw [hquad p hpS, hn]
        linarith only [hrz]
      · rintro ⟨hv, hh⟩
        refine ⟨e.symm v, mem_sphere_zero_iff_norm.mpr ?_, e.right_inv hv⟩
        nlinarith only [hqi v hv, hh, norm_nonneg (e.symm v), (hrb z).1, hrz]
  have hslice (D0 : Set E2) : T '' (D0 ×ˢ ({z} : Set ℝ)) =
      C.symm '' ((e '' (r z • D0)) ×ˢ ({z} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      have hw' : w = z := hw
      subst w
      exact ⟨(e (r z • x), z), ⟨⟨r z • x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨v, w⟩, ⟨⟨p, hp, hpv⟩, hw⟩, rfl⟩
      obtain ⟨x, hx, hxp⟩ := hp
      have hw' : w = z := hw
      subst w
      subst p
      change e (r z • x) = v at hpv
      subst v
      exact ⟨(x, z), ⟨hx, rfl⟩, rfl⟩
  have hcircle : T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
      C.symm '' ({v : E2 | v ∈ e.target ∧ U v = z - d} ×ˢ ({z} : Set ℝ)) := by
    rw [hslice, smul_sphere' (hrb z).1.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos (hrb z).1, mul_one, hslices.2.2]
  refine ⟨?_, ?_, hcircle, ?_⟩
  · rw [hslice, smul_unitClosedBall_of_nonneg (hrb z).1.le, hslices.1]
  · rw [hslice, smul_unitBall_of_pos (hrb z).1, hslices.2.1]
  · rw [hcircle]
    ext y
    constructor
    · rintro ⟨⟨v, w⟩, ⟨⟨hv, hval⟩, hw⟩, rfl⟩
      have hw' : w = z := hw
      subst w
      have hv0 : v ∈ e0.target := by
        rw [hrestrict] at hv
        exact hv.1
      have hvD := htargetD hv0
      have hn := mem_ball_zero_iff.mp hvD
      have hnorm : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
        simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      have hrad : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith only [hn, norm_nonneg v]
      have hheightEq : z - (v 0) ^ 2 - (v 1) ^ 2 - v 0 / 32 - d =
          Real.sqrt (1 - ‖v‖ ^ 2) := by
        dsimp only [U] at hval
        rw [hnorm] at hval ⊢
        linarith only [hval]
      refine ⟨?_, ?_⟩
      · rw [(nestedReferenceBallChart_regions d).2.2.2 _ |>.2.2]
        change (v 0) ^ 2 + (v 1) ^ 2 +
          (z - (v 0) ^ 2 - (v 1) ^ 2 - v 0 / 32 - d) ^ 2 = 1
        rw [hheightEq, Real.sq_sqrt hrad, hnorm]
        ring
      · change (C (C.symm (v, z))).2 = z
        rw [C.apply_symm_apply]
    · rintro ⟨hy, hheightEq⟩
      change (C y).2 = z at hheightEq
      have hthreshold : mu - 9 * rho ^ 2 + d ≤ (C y).2 := by
        have hh := hz.1
        dsimp only [nu, delta] at hh
        rw [hheightEq]
        nlinarith only [hh, hrho2]
      obtain ⟨hv0, _hbound, hyGraph⟩ := (hwhole d).1 y hy hthreshold
      change y = C.symm ((C y).1, U (C y).1 + d) at hyGraph
      have hval : U (C y).1 = z - d := by
        have hh := congrArg (fun y : E3 => (C y).2) hyGraph
        rw [C.apply_symm_apply, hheightEq] at hh
        linarith only [hh]
      have hq := hquad0 (e0.symm (C y).1) (e0.map_target hv0)
      rw [e0.right_inv hv0, hval] at hq
      have hnormInv : ‖e0.symm (C y).1‖ < 3 * rho := by
        nlinarith only [hq, hrz, (hrb z).2.1, norm_nonneg (e0.symm (C y).1),
          hrho, hrho2]
      have hv : (C y).1 ∈ e.target := by
        rw [htarget]
        exact ⟨e0.symm (C y).1, mem_ball_zero_iff.mpr hnormInv, e0.right_inv hv0⟩
      refine ⟨((C y).1, z), ⟨⟨hv, hval⟩, rfl⟩, ?_⟩
      rw [← hheightEq, Prod.eta, C.symm_apply_apply]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
