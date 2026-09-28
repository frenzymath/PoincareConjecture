import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerRadialFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_joint_radial_filling
    (rho : ℝ × ℝ → ℝ)
    (hrho : ContDiffOn ℝ ∞ rho
      (Ioo (-3 / 2 : ℝ) (3 / 2) ×ˢ
        Ioo (17 / 16 - 1 / 8192 : ℝ) (17 / 16 + 1 / 8192)))
    (hbound : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ
        Ioo (17 / 16 - 1 / 8192 : ℝ) (17 / 16 + 1 / 8192),
      1 / 4 < rho p ∧ rho p < 2)
    (hdecrease : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ
        Ioo (17 / 16 - 1 / 8192 : ℝ) (17 / 16 + 1 / 8192),
      deriv (fun h : ℝ => rho (p.1, h)) p.2 ≤ 0) :
    let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
    ∃ F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1) ∧
      ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1) ∧
      (∃ C : Set E2, IsCompact C ∧
        C ⊆ {v : E2 | 1 / 8 < ‖v‖ ∧ ‖v‖ < 4} ∧
        ∀ h : ℝ,
          tsupport (fun v : E2 => F h v - v) ⊆ C ∧
          tsupport (fun v : E2 => (F h).symm v - v) ⊆ C) ∧
      (∀ (h : ℝ) (v : E2), ‖v‖ ≤ 1 / 8 → F h v = v ∧ (F h).symm v = v) ∧
      (∀ h ∈ J,
        F h '' ball (0 : E2) 1 = {v : E2 | ‖v‖ < rho (v 0 / ‖v‖, h)} ∧
        F h '' closedBall (0 : E2) 1 = {v : E2 | ‖v‖ ≤ rho (v 0 / ‖v‖, h)} ∧
        F h '' sphere (0 : E2) 1 = {v : E2 | ‖v‖ = rho (v 0 / ‖v‖, h)}) ∧
      ∀ e : E2, ‖e‖ = 1 →
        ∃ p : ℝ × ℝ → ℝ,
          ContDiff ℝ ∞ p ∧
          (∀ h : ℝ, StrictMono (fun r : ℝ => p (h, r)) ∧ p (h, 0) = 0) ∧
          (∀ (h r : ℝ), 0 < r → F h (r • e) = p (h, r) • e) ∧
          (∀ h ∈ J, p (h, 1) = rho (e 0, h)) ∧
          (∀ h r : ℝ, 0 < deriv (fun s : ℝ => p (h, s)) r) ∧
          ∀ h ∈ J, ∀ r : ℝ, 0 < r → deriv (fun s : ℝ => p (s, r)) h ≤ 0 := by
  classical
  let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
  let Jo : Set ℝ := Ioo (17 / 16 - 1 / 8192) (17 / 16 + 1 / 8192)
  obtain ⟨cl, hcl, hclRange, hclEq⟩ := exists_saddle_end_height_clamp
    (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384) (1 / 32768)
    (by norm_num) (by norm_num)
  have hclJo (h : ℝ) : cl h ∈ Jo := by
    have hh := hclRange h
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hclJ (h : ℝ) (hh : h ∈ J) : cl h = h := hclEq ⟨hh.1.le, hh.2.le⟩
  let theta : E2 → ℝ := fun v => v 0 / ‖v‖
  have htheta (v : E2) : theta v ∈ Icc (-1 : ℝ) 1 := by
    have hn : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hcoord : -‖v‖ ≤ v 0 ∧ v 0 ≤ ‖v‖ := by
      constructor <;> nlinarith only [hn, norm_nonneg v, sq_nonneg (v 1)]
    by_cases hv : v = 0
    · simp only [theta, hv, norm_zero, div_zero]
      norm_num
    · have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
      exact ⟨(le_div_iff₀ hp).mpr (by simpa only [neg_mul, one_mul] using hcoord.1),
        (div_le_iff₀ hp).mpr (by simpa only [one_mul] using hcoord.2)⟩
  have hthetai (v : E2) : theta v ∈ Ioo (-3 / 2 : ℝ) (3 / 2) :=
    ⟨by linarith [(htheta v).1], by linarith [(htheta v).2]⟩
  have hunitTheta (e : E2) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) :
      theta (r • e) = e 0 := by
    change r * e 0 / ‖r • e‖ = e 0
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, he, mul_one]
    field_simp [hr.ne']
  have hunitAngle (e : E2) (he : ‖e‖ = 1) : e 0 ∈ Icc (-1 : ℝ) 1 := by
    simpa only [theta, he, div_one] using htheta e
  let K0 : Set E2 := {v | 1 / 4 ≤ ‖v‖ ∧ ‖v‖ ≤ 2}
  let U0 : Set E2 := {v | 1 / 8 < ‖v‖ ∧ ‖v‖ < 4}
  have hK0 : IsCompact K0 := (isCompact_closedBall (0 : E2) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun v hv => mem_closedBall_zero_iff.mpr hv.2)
  have hU0 : IsOpen U0 := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  obtain ⟨chi, hchi, hcchi, hsChi, hnear, hRange⟩ :=
    exists_compact_smooth_cutoff hK0 hU0
      (fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩)
  have hchiOne (v : E2) (hv : v ∈ K0) : chi v = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnear v hv).self_of_nhds
  let V : E2 → E2 := fun v => chi v • v
  have hV : ContDiff ℝ ∞ V := hchi.smul contDiff_id
  have hcV : HasCompactSupport V := hcchi.smul_right
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds V hV hcV
  let Phi : E2 → ℝ → E2 := boundedFlow V hK hL
  have hPhi : ContDiff ℝ ∞ (fun p : E2 × ℝ => Phi p.1 p.2) :=
    boundedFlow_contDiff V hK hL hV hcV
  have hzero : V 0 = 0 := by simp only [V, smul_zero]
  have hPhiZero (s : ℝ) : Phi 0 s = 0 := boundedFlow_eq_self V hK hL 0 hzero s
  have hPhiFixed (v : E2) (hv : v ∉ tsupport chi) (s : ℝ) : Phi v s = v :=
    boundedFlow_eq_self V hK hL v
      (by simp only [V, image_eq_zero_of_notMem_tsupport hv, zero_smul]) s
  have hsmall (v : E2) (hv : ‖v‖ ≤ 1 / 8) : v ∉ tsupport chi := by
    intro hc
    exact (hsChi hc).1.not_ge hv

  have hRay (e : E2) (he : ‖e‖ = 1) :
      ∃ f : ℝ × ℝ → ℝ,
        ContDiff ℝ ∞ f ∧
        (∀ t : ℝ, StrictMono (fun r : ℝ => f (r, t))) ∧
        (∀ t : ℝ, f (0, t) = 0) ∧
        (∀ (r : ℝ), 0 < r → ∀ t : ℝ, Phi (r • e) t = f (r, t) • e) ∧
        (∀ r t : ℝ, f (f (r, t), -t) = r) ∧
        (∀ r t : ℝ, HasDerivAt (fun s : ℝ => f (r, s))
          (chi (f (r, t) • e) * f (r, t)) t) ∧
        ∀ t r : ℝ, 0 < deriv (fun s : ℝ => f (s, t)) r := by
    let v : ℝ → ℝ := fun r => chi (r • e) * r
    have hv : ContDiff ℝ ∞ v :=
      (hchi.comp (contDiff_id.smul contDiff_const)).mul contDiff_id
    have hvs : Function.support v ⊆ Icc (-4 : ℝ) 4 := by
      intro r hr
      have hc : chi (r • e) ≠ 0 := by
        intro hh
        exact hr (by simp only [v, hh, zero_mul])
      have hp := hsChi (subset_tsupport chi hc)
      have hh : |r| < 4 := by
        simpa only [norm_smul, Real.norm_eq_abs, he, mul_one] using hp.2
      exact ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩
    have hvc : HasCompactSupport v :=
      (isCompact_Icc : IsCompact (Icc (-4 : ℝ) 4)).of_isClosed_subset
        (isClosed_tsupport v) (closure_minimal hvs isClosed_Icc)
    obtain ⟨Kv, Lv, hKv, hLv⟩ := compactField_bounds v hv hvc
    let f : ℝ × ℝ → ℝ := fun p => boundedFlow v hKv hLv p.1 p.2
    have hf : ContDiff ℝ ∞ f := boundedFlow_contDiff v hKv hLv hv hvc
    have hm (t : ℝ) : StrictMono (fun r : ℝ => f (r, t)) :=
      boundedFlow_strictMono v hKv hLv hv hvc t
    have hz (t : ℝ) : f (0, t) = 0 :=
      boundedFlow_eq_self v hKv hLv 0 (by simp only [v, mul_zero]) t
    have hrep (r : ℝ) (_hr : 0 < r) (s : ℝ) :
        Phi (r • e) s = f (r, s) • e := by
      have hd (t : ℝ) : HasDerivAt (fun q : ℝ => f (r, q) • e)
          (V (f (r, t) • e)) t := by
        simpa only [V, v, smul_smul] using
          (boundedFlow_hasDerivAt v hKv hLv r t).smul_const e
      have hh := boundedField_solution_unique V hK
        (boundedFlow_hasDerivAt V hK hL (r • e)) hd
        (by simp only [f, boundedFlow_zero])
      exact congrFun hh s
    have hinv (r t : ℝ) : f (f (r, t), -t) = r := boundedFlow_neg v hKv hLv r t
    have hd (t r : ℝ) : DifferentiableAt ℝ (fun s : ℝ => f (s, t)) r :=
      ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) r
    refine ⟨f, hf, hm, hz, hrep, hinv, fun r t => boundedFlow_hasDerivAt v hKv hLv r t, ?_⟩
    intro t r
    have hchain := (hd (-t) (f (r, t))).hasDerivAt.comp r (hd t r).hasDerivAt
    have hid : (fun s : ℝ => f (f (s, t), -t)) = id := funext (fun s => hinv s t)
    change HasDerivAt (fun s : ℝ => f (f (s, t), -t)) _ r at hchain
    rw [hid] at hchain
    have hprod := hchain.unique (hasDerivAt_id r)
    have hnz : deriv (fun s : ℝ => f (s, t)) r ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hprod
      norm_num at hprod
    exact lt_of_le_of_ne (hm t).monotone.deriv_nonneg (Ne.symm hnz)
  have hnormal (v : E2) (hv : v ≠ 0) :
      ‖‖v‖⁻¹ • v‖ = 1 ∧ ‖v‖ • (‖v‖⁻¹ • v) = v := by
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    constructor
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
      exact inv_mul_cancel₀ hp.ne'
    · rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  have hPhiTheta (v : E2) (s : ℝ) : theta (Phi v s) = theta v := by
    by_cases hv : v = 0
    · simp only [hv, hPhiZero]
    · obtain ⟨he, hve⟩ := hnormal v hv
      obtain ⟨f, _hf, hm, hz, hrep, _hinv, _hd, _hpos⟩ := hRay _ he
      have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hp : 0 < f (‖v‖, s) := by
        have hh := hm s hr
        change f (0, s) < f (‖v‖, s) at hh
        rwa [hz] at hh
      have hangle : (‖v‖⁻¹ • v) 0 = theta v := by
        change ‖v‖⁻¹ * v 0 = v 0 / ‖v‖
        ring
      calc
        theta (Phi v s) = theta (Phi (‖v‖ • (‖v‖⁻¹ • v)) s) :=
          congrArg (fun x => theta (Phi x s)) hve.symm
        _ = (‖v‖⁻¹ • v) 0 := by rw [hrep _ hr, hunitTheta _ he _ hp]
        _ = theta v := hangle
  let a : ℝ → E2 → ℝ := fun h v => Real.log (rho (theta v, cl h))
  have hrhop (h : ℝ) (v : E2) : 0 < rho (theta v, cl h) := by
    linarith [(hbound (theta v, cl h) ⟨htheta v, hclJo h⟩).1]
  let G : ℝ → E2 → E2 := fun h v => Phi v (a h v)
  let Gi : ℝ → E2 → E2 := fun h v => Phi v (-a h v)
  have hleft (h : ℝ) (v : E2) : Gi h (G h v) = v := by
    have ha : a h (G h v) = a h v := by
      dsimp only [a, G]
      rw [hPhiTheta]
    dsimp only [Gi]
    rw [ha]
    exact boundedFlow_neg V hK hL v (a h v)
  have hright (h : ℝ) (v : E2) : G h (Gi h v) = v := by
    have ha : a h (Gi h v) = a h v := by
      dsimp only [a, Gi]
      rw [hPhiTheta]
    dsimp only [G]
    rw [ha]
    simpa only [neg_neg] using boundedFlow_neg V hK hL v (-a h v)
  have hGa (sgn : ℝ) : ContDiff ℝ ∞
      (fun p : E2 × ℝ => Phi p.1 (sgn * a p.2 p.1)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.1 = 0
    · have hn : ∀ᶠ q : E2 × ℝ in 𝓝 p, ‖q.1‖ < 1 / 8 :=
        (continuous_norm.comp continuous_fst).continuousAt.eventually
          (gt_mem_nhds (by change ‖p.1‖ < 1 / 8; rw [hp, norm_zero]; norm_num))
      have heq : (fun q : E2 × ℝ => Phi q.1 (sgn * a q.2 q.1)) =ᶠ[𝓝 p]
          (fun q : E2 × ℝ => q.1) := by
        filter_upwards [hn] with q hq
        exact hPhiFixed q.1 (hsmall q.1 hq.le) _
      exact contDiffAt_fst.congr_of_eventuallyEq heq
    · have hth : ContDiffAt ℝ ∞ (fun q : E2 × ℝ => theta q.1) p :=
        (((EuclideanSpace.proj 0).contDiff.comp contDiff_fst).contDiffAt).div
          ((contDiffAt_norm ℝ hp).comp p contDiffAt_fst) (norm_ne_zero_iff.mpr hp)
      have harg : ContDiffAt ℝ ∞
          (fun q : E2 × ℝ => (theta q.1, cl q.2)) p :=
        hth.prodMk (hcl.contDiffAt.comp p contDiffAt_snd)
      have hr : ContDiffAt ℝ ∞ (fun q : E2 × ℝ => rho (theta q.1, cl q.2)) p :=
        (hrho.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
          ⟨hthetai p.1, hclJo p.2⟩)).comp p harg
      exact hPhi.contDiffAt.comp p
        (contDiffAt_fst.prodMk (contDiffAt_const.mul (hr.log (hrhop _ _).ne')))
  have hG : ContDiff ℝ ∞ (fun p : E2 × ℝ => G p.2 p.1) := by
    simpa only [one_mul, G] using hGa 1
  have hGi : ContDiff ℝ ∞ (fun p : E2 × ℝ => Gi p.2 p.1) := by
    simpa only [neg_one_mul, Gi] using hGa (-1)
  let F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := fun h => {
    toEquiv := { toFun := G h, invFun := Gi h, left_inv := hleft h, right_inv := hright h }
    contMDiff_toFun := (hG.comp (contDiff_id.prodMk contDiff_const)).contMDiff
    contMDiff_invFun := (hGi.comp (contDiff_id.prodMk contDiff_const)).contMDiff }
  have hF (h : ℝ) (v : E2) : F h v = Phi v (a h v) := rfl
  have hFi (h : ℝ) (v : E2) : (F h).symm v = Phi v (-a h v) := rfl
  have hFizero (h : ℝ) : (F h).symm 0 = 0 := hPhiZero _
  have hsupport (h : ℝ) :
      tsupport (fun v : E2 => F h v - v) ⊆ tsupport chi ∧
      tsupport (fun v : E2 => (F h).symm v - v) ⊆ tsupport chi := by
    constructor <;> apply closure_minimal _ (isClosed_tsupport chi)
    · intro v hv
      by_contra hh
      exact hv (sub_eq_zero.mpr (hPhiFixed v hh _))
    · intro v hv
      by_contra hh
      exact hv (sub_eq_zero.mpr (hPhiFixed v hh _))
  have hunitTrack (e : E2) (he : ‖e‖ = 1) (R : ℝ) (hR : 1 / 4 < R ∧ R < 2) :
      Phi e (Real.log R) = R • e := by
    let b := Real.log R
    have hRp : 0 < R := by linarith [hR.1]
    have heb : Real.exp b = R := Real.exp_log hRp
    have htrack (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        Real.exp (s * b) • e ∈ K0 := by
      change 1 / 4 ≤ ‖Real.exp (s * b) • e‖ ∧ ‖Real.exp (s * b) • e‖ ≤ 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he, mul_one]
      by_cases hb : 0 ≤ b
      · have hlo : (1 : ℝ) ≤ Real.exp (s * b) :=
          Real.one_le_exp_iff.mpr (mul_nonneg hs.1 hb)
        have hhi : Real.exp (s * b) ≤ R := by
          rw [← heb]
          exact Real.exp_le_exp.mpr (by nlinarith only [hs.2, hb])
        exact ⟨by linarith only [hlo], hhi.trans hR.2.le⟩
      · have hb' : b ≤ 0 := (lt_of_not_ge hb).le
        have hlo : R ≤ Real.exp (s * b) := by
          rw [← heb]
          exact Real.exp_le_exp.mpr (by nlinarith only [hs.2, hb'])
        have hhi : Real.exp (s * b) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs.1 hb')
        exact ⟨hR.1.le.trans hlo, by linarith only [hhi]⟩
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun t : ℝ => Real.exp (t * b) • e)
          (b • V (Real.exp (s * b) • e)) s := by
      simp only [V, hchiOne _ (htrack s hs), smul_smul]
      simpa only [one_mul, id_eq, mul_comm] using
        (((hasDerivAt_id s).mul_const b).exp.smul_const e)
    have hpd (s : ℝ) : HasDerivAt (fun t : ℝ => Phi e (t * b))
        (b • V (Phi e (s * b))) s := by
      simpa only [one_mul, id_eq, Function.comp_def] using
        (boundedFlow_hasDerivAt V hK hL e (s * b)).scomp s
          ((hasDerivAt_id s).mul_const b)
    have hscaled : LipschitzWith (‖b‖₊ * K) (fun v : E2 => b • V v) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm,
        mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using hK.dist_le_mul x y) (norm_nonneg b)
    have heq : EqOn (fun s : ℝ => Phi e (s * b))
        (fun s : ℝ => Real.exp (s * b) • e) (Icc (0 : ℝ) 1) := by
      apply ODE_solution_unique_of_mem_Icc_right
        (v := fun _ v => b • V v) (s := fun _ => univ)
        (fun _ _ => hscaled.lipschitzOnWith)
      · exact fun s _ => (hpd s).continuousAt.continuousWithinAt
      · exact fun s _ => (hpd s).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
      · exact fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · simp only [Phi, boundedFlow_zero, zero_mul, Real.exp_zero, one_smul]
    simpa only [one_mul, heb] using heq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hFamilyRay (e : E2) (he : ‖e‖ = 1) :
      ∃ p : ℝ × ℝ → ℝ,
        ContDiff ℝ ∞ p ∧
        (∀ h : ℝ, StrictMono (fun r : ℝ => p (h, r)) ∧ p (h, 0) = 0) ∧
        (∀ (h r : ℝ), 0 < r → F h (r • e) = p (h, r) • e) ∧
        (∀ h ∈ J, p (h, 1) = rho (e 0, h)) ∧
        (∀ h r : ℝ, 0 < deriv (fun s : ℝ => p (h, s)) r) ∧
        ∀ h ∈ J, ∀ r : ℝ, 0 < r → deriv (fun s : ℝ => p (s, r)) h ≤ 0 := by
    obtain ⟨f, hf, hm, hz, hrep, _hinv, hd, hpos⟩ := hRay e he
    let b : ℝ → ℝ := fun h => Real.log (rho (e 0, cl h))
    have hangle : e 0 ∈ Ioo (-3 / 2 : ℝ) (3 / 2) :=
      ⟨by linarith [(hunitAngle e he).1], by linarith [(hunitAngle e he).2]⟩
    have hrp (h : ℝ) : 0 < rho (e 0, cl h) := by
      linarith [(hbound (e 0, cl h) ⟨hunitAngle e he, hclJo h⟩).1]
    have hr : ContDiff ℝ ∞ (fun h : ℝ => rho (e 0, cl h)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro h
      exact (hrho.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        ⟨hangle, hclJo h⟩)).comp h (contDiffAt_const.prodMk hcl.contDiffAt)
    have hb : ContDiff ℝ ∞ b := hr.log (fun h => (hrp h).ne')
    let p : ℝ × ℝ → ℝ := fun q => f (q.2, b q.1)
    have hp : ContDiff ℝ ∞ p := hf.comp (contDiff_snd.prodMk (hb.comp contDiff_fst))
    have hpr (h r : ℝ) (hr : 0 < r) : F h (r • e) = p (h, r) • e := by
      rw [hF]
      dsimp only [a]
      rw [hunitTheta e he r hr]
      exact hrep r hr (b h)
    have hpu (h : ℝ) (hh : h ∈ J) : p (h, 1) = rho (e 0, h) := by
      have ha : a h e = Real.log (rho (e 0, h)) := by
        dsimp only [a, theta]
        rw [he, div_one, hclJ h hh]
      have hmemb : (e 0, h) ∈ Icc (-1 : ℝ) 1 ×ˢ Jo :=
        ⟨hunitAngle e he, by rw [← hclJ h hh]; exact hclJo h⟩
      have hu := hpr h 1 (by norm_num)
      rw [one_smul, hF, ha, hunitTrack e he _ (hbound _ hmemb)] at hu
      have hpp : 0 < p (h, 1) := by
        have hh := hm (b h) (by norm_num : (0 : ℝ) < 1)
        change f (0, b h) < p (h, 1) at hh
        rwa [hz] at hh
      have hrr : 0 < rho (e 0, h) := by linarith [(hbound _ hmemb).1]
      have hn := congrArg norm hu
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hrr, abs_of_pos hpp, he, mul_one, mul_one] at hn
      exact hn.symm
    refine ⟨p, hp, fun h => ⟨hm (b h), hz (b h)⟩, hpr, hpu,
      fun h r => hpos (b h) r, ?_⟩
    intro h hh r hr0
    have hrhoAt : DifferentiableAt ℝ (fun s : ℝ => rho (e 0, s)) h :=
      (((hrho.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        ⟨hangle, by rw [← hclJ h hh]; exact hclJo h⟩)).comp h
          (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))
    have hclNear : cl =ᶠ[𝓝 h] id := by
      filter_upwards [isOpen_Ioo.mem_nhds hh] with s hs
      exact hclJ s hs
    have hbn : b =ᶠ[𝓝 h] (fun s : ℝ => Real.log (rho (e 0, s))) := by
      filter_upwards [hclNear] with s hs
      simp only [b, hs, id_eq]
    have hrr : 0 < rho (e 0, h) := by rw [← hclJ h hh]; exact hrp h
    have hbder : HasDerivAt b
        (deriv (fun s : ℝ => rho (e 0, s)) h / rho (e 0, h)) h :=
      (hrhoAt.hasDerivAt.log hrr.ne').congr_of_eventuallyEq hbn
    have hpd := (hd r (b h)).comp h hbder
    have hp0 : 0 < p (h, r) := by
      have hh := hm (b h) hr0
      change f (0, b h) < p (h, r) at hh
      rwa [hz] at hh
    have hchi0 : 0 ≤ chi (p (h, r) • e) := (hRange _).1
    have hdr := hdecrease (e 0, h)
      ⟨hunitAngle e he, by rw [← hclJ h hh]; exact hclJo h⟩
    change HasDerivAt (fun s : ℝ => p (s, r)) _ h at hpd
    rw [hpd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hchi0 hp0.le)
      (div_nonpos_of_nonpos_of_nonneg hdr hrr.le)
  refine ⟨F, hG, hGi, ⟨tsupport chi, hcchi, hsChi, hsupport⟩,
    fun h v hv => ⟨hPhiFixed v (hsmall v hv) _, hPhiFixed v (hsmall v hv) _⟩,
    ?_, hFamilyRay⟩
  intro h hh
  have himage (T : Set E2) (v : E2) : v ∈ F h '' T ↔ (F h).symm v ∈ T := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [(F h).symm_apply_apply] using hq
    · intro hv
      exact ⟨(F h).symm v, hv, (F h).apply_symm_apply v⟩
  have htest (v : E2) :
      (‖(F h).symm v‖ < 1 ↔ ‖v‖ < rho (theta v, h)) ∧
      (‖(F h).symm v‖ ≤ 1 ↔ ‖v‖ ≤ rho (theta v, h)) ∧
      (‖(F h).symm v‖ = 1 ↔ ‖v‖ = rho (theta v, h)) := by
    by_cases hv : v = 0
    · have hrp : 0 < rho (theta (0 : E2), h) := by
        rw [← hclJ h hh]
        exact hrhop h 0
      simp only [hv, hFizero, norm_zero, zero_lt_one, hrp, zero_le_one,
        hrp.le, zero_ne_one, hrp.ne, iff_self, and_self]
    · let r := ‖v‖
      let e : E2 := r⁻¹ • v
      obtain ⟨he, hre⟩ := hnormal v hv
      change ‖e‖ = 1 at he
      change r • e = v at hre
      have hr : 0 < r := norm_pos_iff.mpr hv
      obtain ⟨f, _hf, hm, hz, hrep, _hinv, _hd, _hpos⟩ := hRay e he
      let q := f (r, -a h v)
      have hq : 0 < q := by
        have hh := hm (-a h v) hr
        change f (0, -a h v) < q at hh
        rwa [hz] at hh
      have hpre : (F h).symm v = q • e := by
        rw [hFi]
        exact (congrArg (fun x => Phi x (-a h v)) hre.symm).trans
          (hrep r hr (-a h v))
      have hn : ‖(F h).symm v‖ = q := by
        rw [hpre, norm_smul, Real.norm_eq_abs, abs_of_pos hq, he, mul_one]
      obtain ⟨p, _hp, hpm, hpr, hpu, _hpd, _hph⟩ := hFamilyRay e he
      have hpq : p (h, q) = r := by
        have hfwd := (F h).apply_symm_apply v
        rw [hpre, hpr h q hq, ← hre] at hfwd
        have hqp : 0 < p (h, q) := by
          have hh := (hpm h).1 hq
          change p (h, 0) < p (h, q) at hh
          rwa [(hpm h).2] at hh
        have hn := congrArg norm hfwd
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hqp,
          abs_of_pos hr, he, mul_one] using hn
      have hae : e 0 = theta v := by
        rw [← hre, hunitTheta e he r hr]
      have hu : p (h, 1) = rho (theta v, h) := by rw [hpu h hh, hae]
      rw [hn]
      refine ⟨?_, ?_, ?_⟩
      · rw [← (hpm h).1.lt_iff_lt, hpq, hu]
      · rw [← (hpm h).1.le_iff_le, hpq, hu]
      · rw [← (hpm h).1.injective.eq_iff, hpq, hu]
  constructor
  · ext v
    rw [himage, mem_ball_zero_iff]
    exact (htest v).1
  · constructor
    · ext v
      rw [himage, mem_closedBall_zero_iff]
      exact (htest v).2.1
    · ext v
      rw [himage, mem_sphere_zero_iff_norm]
      exact (htest v).2.2

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
