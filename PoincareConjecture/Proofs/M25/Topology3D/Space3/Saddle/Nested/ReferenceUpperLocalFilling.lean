import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighCritical
import PoincareConjecture.Proofs.M25.Topology3D.Space3.MorseChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

open Set Metric
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_upper_reference_local_filling :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let L : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    ∃ ws wm : ℝ,
      1 / 2 < ws ∧ ws < 3 / 4 ∧ g ws = 1 / 32 ∧
      0 < wm ∧ wm < 1 / 2 ∧ g wm = -(1 / 32) ∧
      let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
      let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
      let k : ℝ := U vs
      let mu : ℝ := U vm
      ∃ (rho : ℝ) (e0 e : OpenPartialHomeomorph E2 E2),
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
        ∀ d : ℝ,
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
                Metric.closedBall (0 : E2) (Real.sqrt (mu - h)) := by
  classical
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let L : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  obtain ⟨ws, wm, hwslo, hwsup, hwsroot, hwmp, hwmh, hwmroot,
    hvs, hvm, hklo, hkhi, hmulo, hsmooth, hcrit, hmax, hunique,
    _hclass, _hpositive, hinj⟩ := exists_reference_high_critical_geometry
  let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  let k := U vs
  let mu := U vm
  change (37 : ℝ) / 32 < k at hklo
  change k < 5 / 4 at hkhi
  change (5 : ℝ) / 4 < mu at hmulo
  change ContDiffOn ℝ ∞ U (ball (0 : E2) 1) at hsmooth
  change fderiv ℝ U vm = 0 at hcrit
  change ∀ v ∈ closedBall (0 : E2) 1, U v ≤ mu at hmax
  change ∀ v ∈ closedBall (0 : E2) 1, U v = mu ↔ v = vm at hunique
  have hcritNeg : fderiv ℝ (fun v : E2 => -U v) vm = 0 := by
    change fderiv ℝ (-U) vm = 0
    rw [fderiv_neg, hcrit, neg_zero]
  obtain ⟨sigma, tau, eM, hsigma, htau, hvmS, hMS, hMzero, hM, hMi, hMform⟩ :=
    exists_morse_chart (finrank_euclideanSpace_fin (n := 2)) (fun v : E2 => -U v)
      isOpen_ball hsmooth.neg vm (mem_ball_zero_iff.mpr hvm) hcritNeg hinj
  have h0T : (0 : ℝ × ℝ) ∈ eM.target := hMzero ▸ eM.map_source hvmS
  obtain ⟨a, ha, haT⟩ := Metric.isOpen_iff.mp eM.open_target 0 h0T
  have haxis0 : (a / 2, (0 : ℝ)) ∈ eM.target := by
    apply haT
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_zero, abs_of_pos (by linarith only [ha])]
    constructor <;> linarith only [ha]
  have haxis1 : ((0 : ℝ), a / 2) ∈ eM.target := by
    apply haT
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_zero, abs_of_pos (by linarith only [ha])]
    constructor <;> linarith only [ha]
  have hsign0 : sigma = 1 := by
    have hf := hMform (eM.symm (a / 2, 0)) (eM.map_target haxis0)
    rw [eM.right_inv haxis0] at hf
    have hm := hmax (eM.symm (a / 2, 0))
      (ball_subset_closedBall (hMS (eM.map_target haxis0)))
    change -U (eM.symm (a / 2, 0)) = -mu + sigma * (a / 2) ^ 2 + tau * 0 ^ 2 at hf
    rcases mul_self_eq_one_iff.mp hsigma with hs | hs
    · exact hs
    · rw [hs] at hf
      nlinarith only [hf, hm, ha]
  have hsign1 : tau = 1 := by
    have hf := hMform (eM.symm (0, a / 2)) (eM.map_target haxis1)
    rw [eM.right_inv haxis1] at hf
    have hm := hmax (eM.symm (0, a / 2))
      (ball_subset_closedBall (hMS (eM.map_target haxis1)))
    change -U (eM.symm (0, a / 2)) = -mu + sigma * 0 ^ 2 + tau * (a / 2) ^ 2 at hf
    rcases mul_self_eq_one_iff.mp htau with hs | hs
    · exact hs
    · rw [hs] at hf
      nlinarith only [hf, hm, ha]
  let P : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let e0 : OpenPartialHomeomorph E2 E2 :=
    P.toHomeomorph.transOpenPartialHomeomorph eM.symm
  have h0S : (0 : E2) ∈ e0.source := by
    change P 0 ∈ eM.target
    simpa only [map_zero] using h0T
  have hzero : e0 0 = vm := by
    change eM.symm (P 0) = vm
    rw [map_zero, ← hMzero, eM.left_inv hvmS]
  have hvmT : vm ∈ e0.target := hvmS
  have htargetD : e0.target ⊆ ball (0 : E2) 1 := hMS
  have he0 : ContDiffOn ℝ ∞ e0 e0.source :=
    hMi.comp P.contDiff.contDiffOn (fun _ hx => hx)
  have he0i : ContDiffOn ℝ ∞ e0.symm e0.target :=
    P.symm.contDiff.comp_contDiffOn hM
  have hnorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hquad (p : E2) (hp : p ∈ e0.source) : U (e0 p) = mu - ‖p‖ ^ 2 := by
    change P p ∈ eM.target at hp
    have hpNorm : ‖p‖ ^ 2 = (P p).1 ^ 2 + (P p).2 ^ 2 := hnorm p
    have hf := hMform (eM.symm (P p)) (eM.map_target hp)
    rw [eM.right_inv hp, hsign0, hsign1, one_mul, one_mul] at hf
    change U (eM.symm (P p)) = mu - ‖p‖ ^ 2
    rw [hpNorm]
    change -U (eM.symm (P p)) = -mu + (P p).1 ^ 2 + (P p).2 ^ 2 at hf
    linarith only [hf]
  have hcont : Continuous U :=
    ((continuous_norm.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))).add
      ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.div_const 32)
  obtain ⟨eta, heta, hetaS⟩ := Metric.isOpen_iff.mp e0.open_source 0 h0S
  let K : Set E2 := closedBall 0 1 \ e0.target
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : E2) 1).inter_right e0.open_target.isClosed_compl
  let vunit : E2 := !₂[1, 0]
  have hvunit : ‖vunit‖ = 1 := by
    have hs : ‖vunit‖ ^ 2 = 1 := by rw [hnorm]; norm_num [vunit]
    nlinarith only [hs, norm_nonneg vunit]
  have hKnonempty : K.Nonempty := by
    refine ⟨vunit, mem_closedBall_zero_iff.mpr hvunit.le, ?_⟩
    intro ht
    have hh := mem_ball_zero_iff.mp (htargetD ht)
    linarith only [hh, hvunit]
  obtain ⟨vK, hvK, hKmax⟩ := hKcompact.exists_isMaxOn hKnonempty hcont.continuousOn
  have hKlt : U vK < mu := by
    have hh := hmax vK hvK.1
    apply lt_of_le_of_ne hh
    intro he
    have heq := (hunique vK hvK.1).mp he
    exact hvK.2 (heq ▸ hvmT)
  let gap := mu - U vK
  have hgap : 0 < gap := sub_pos.mpr hKlt
  have hmk : 0 < mu - k := by linarith only [hkhi, hmulo]
  let rho := min (eta / 8) (min (Real.sqrt gap / 6) (Real.sqrt (mu - k) / 6))
  have hrho : 0 < rho := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hrhoEta : rho ≤ eta / 8 := min_le_left _ _
  have hrhoGap : rho ≤ Real.sqrt gap / 6 := (min_le_right _ _).trans (min_le_left _ _)
  have hrhoHeight : rho ≤ Real.sqrt (mu - k) / 6 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hradGap : 9 * rho ^ 2 < gap := by
    have hs0 := Real.sqrt_nonneg gap
    have hs2 := Real.sq_sqrt hgap.le
    have hs : (6 * rho) ^ 2 ≤ (Real.sqrt gap) ^ 2 :=
      (sq_le_sq₀ (by positivity) hs0).mpr (by linarith only [hrhoGap])
    nlinarith only [hs, hs2, hgap]
  have hradHeight : k < mu - 9 * rho ^ 2 := by
    have hs0 := Real.sqrt_nonneg (mu - k)
    have hs2 := Real.sq_sqrt hmk.le
    have hs : (6 * rho) ^ 2 ≤ (Real.sqrt (mu - k)) ^ 2 :=
      (sq_le_sq₀ (by positivity) hs0).mpr (by linarith only [hrhoHeight])
    nlinarith only [hs, hs2, hmk]
  have hclosedSource : closedBall (0 : E2) (4 * rho) ⊆ e0.source := by
    intro p hp
    apply hetaS
    rw [mem_ball_zero_iff]
    have hn := mem_closedBall_zero_iff.mp hp
    linarith only [hn, hrhoEta, heta]
  have hsource3 (p : E2) (hp : p ∈ closedBall (0 : E2) (3 * rho)) : p ∈ e0.source :=
    hclosedSource (mem_closedBall_zero_iff.mpr (by
      have hn := mem_closedBall_zero_iff.mp hp
      linarith only [hn, hrho]))
  have hfull (v : E2) (hv : v ∈ closedBall (0 : E2) 1)
      (hval : mu - 9 * rho ^ 2 ≤ U v) :
      v ∈ e0.target ∧ ‖e0.symm v‖ ≤ 3 * rho := by
    have ht : v ∈ e0.target := by
      by_contra hn
      have hh := hKmax (show v ∈ K from ⟨hv, hn⟩)
      change U v ≤ U vK at hh
      dsimp only [gap] at hradGap
      linarith only [hh, hval, hradGap]
    refine ⟨ht, ?_⟩
    have hh := hquad (e0.symm v) (e0.map_target ht)
    rw [e0.right_inv ht] at hh
    nlinarith only [hh, hval, hrho, norm_nonneg (e0.symm v)]
  have hlower (v : E2) (hv : v ∈ closedBall (0 : E2) 1) : L v ≤ 33 / 32 := by
    have hn := mem_closedBall_zero_iff.mp hv
    have hc := (le_abs_self (v 0)).trans ((PiLp.norm_apply_le v 0).trans hn)
    have hs := Real.sqrt_nonneg (1 - ‖v‖ ^ 2)
    change ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 ≤ _
    nlinarith only [hn, norm_nonneg v, hc, hs]
  have hlowerImage (p : E2) (hp : p ∈ closedBall (0 : E2) (3 * rho)) :
      L (e0 p) < mu - 9 * rho ^ 2 := by
    have hh := hlower (e0 p) (ball_subset_closedBall (htargetD (e0.map_source (hsource3 p hp))))
    linarith only [hh, hklo, hradHeight]
  let e := e0.restrOpen (ball 0 (3 * rho)) isOpen_ball
  have heSource : e.source = ball 0 (3 * rho) :=
    inter_eq_right.mpr (fun _ hp => hsource3 _ (ball_subset_closedBall hp))
  have heTarget : e.target = e0 '' ball 0 (3 * rho) := by
    rw [← heSource]
    change e.target = e '' e.source
    exact e.image_source_eq_target.symm
  have he : ContDiffOn ℝ ∞ e e.source := he0.mono inter_subset_left
  have hei : ContDiffOn ℝ ∞ e.symm e.target := he0i.mono inter_subset_left
  have heQuad (p : E2) (hp : p ∈ e.source) : U (e p) = mu - ‖p‖ ^ 2 :=
    hquad p hp.1
  have hshear (q : E3) (d : ℝ) :
      heightCoordinates (nestedReferenceDiffeomorph d q) =
        ((heightCoordinates q).1,
          (heightCoordinates q).2 + ‖(heightCoordinates q).1‖ ^ 2 +
            (heightCoordinates q).1 0 / 32 + d) := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · rw [hnorm]
      change q 2 + (q 0) ^ 2 + (q 1) ^ 2 + q 0 / 32 + d =
        q 2 + ((q 0) ^ 2 + (q 1) ^ 2) + q 0 / 32 + d
      ring
  have hgraphMem (d : ℝ) (v : E2) (hv : v ∈ ball (0 : E2) 1) :
      heightCoordinates.symm (v, U v + d) ∈ (nestedReferenceBallChart d).boundary := by
    let q := heightCoordinates.symm (v, Real.sqrt (1 - ‖v‖ ^ 2))
    have hrad : 0 ≤ 1 - ‖v‖ ^ 2 := by
      have hn := mem_ball_zero_iff.mp hv
      nlinarith only [hn, norm_nonneg v]
    have hq : q ∈ sphere (0 : E3) 1 := by
      rw [mem_sphere_zero_iff_norm]
      have hs : ‖q‖ ^ 2 = 1 := by
        rw [heightCoordinates_symm_norm_sq, Real.sq_sqrt hrad]
        ring
      nlinarith only [hs, norm_nonneg q]
    refine ⟨q, hq, ?_⟩
    change nestedReferenceDiffeomorph d q = _
    apply heightCoordinates.injective
    rw [hshear]
    simp only [q, heightCoordinates.apply_symm_apply]
    change (v, Real.sqrt (1 - ‖v‖ ^ 2) + ‖v‖ ^ 2 + v 0 / 32 + d) = (v, U v + d)
    congr 1
    dsimp only [U]
    ring
  have hwhole (d : ℝ) (y : E3) (hy : y ∈ (nestedReferenceBallChart d).boundary)
      (hh : mu - 9 * rho ^ 2 + d ≤ (heightCoordinates y).2) :
      (heightCoordinates y).1 ∈ e0.target ∧
      ‖e0.symm (heightCoordinates y).1‖ ≤ 3 * rho ∧
      y = heightCoordinates.symm ((heightCoordinates y).1, U (heightCoordinates y).1 + d) := by
    rcases hy with ⟨q, hq, rfl⟩
    change mu - 9 * rho ^ 2 + d ≤
      (heightCoordinates (nestedReferenceDiffeomorph d q)).2 at hh
    rw [hshear] at hh
    let v := (heightCoordinates q).1
    let w := (heightCoordinates q).2
    have hqnorm := mem_sphere_zero_iff_norm.mp hq
    have hvw : ‖v‖ ^ 2 + w ^ 2 = 1 := by
      have hn := heightCoordinates_norm_sq q
      rw [hqnorm] at hn
      simpa only [one_pow] using hn.symm
    have hv : v ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr (by
      nlinarith only [hvw, sq_nonneg w, norm_nonneg v])
    have hc : v 0 ≤ 1 :=
      (le_abs_self _).trans ((PiLp.norm_apply_le v 0).trans (mem_closedBall_zero_iff.mp hv))
    have hwp : 0 < w := by
      change mu - 9 * rho ^ 2 + d ≤ w + ‖v‖ ^ 2 + v 0 / 32 + d at hh
      by_contra hn
      have hw : w ≤ 0 := le_of_not_gt hn
      nlinarith only [hh, hc, hvw, sq_nonneg w, hw, hklo, hradHeight]
    have hwEq : w = Real.sqrt (1 - ‖v‖ ^ 2) := by
      have hs := Real.sq_sqrt (show 0 ≤ 1 - ‖v‖ ^ 2 by nlinarith only [hvw, sq_nonneg w])
      have hn := Real.sqrt_nonneg (1 - ‖v‖ ^ 2)
      nlinarith only [hs, hn, hvw, hwp]
    have hval : mu - 9 * rho ^ 2 ≤ U v := by
      change mu - 9 * rho ^ 2 + d ≤ w + ‖v‖ ^ 2 + v 0 / 32 + d at hh
      rw [hwEq] at hh
      dsimp only [U]
      linarith only [hh]
    obtain ⟨ht, hnormInv⟩ := hfull v hv hval
    change (heightCoordinates (nestedReferenceDiffeomorph d q)).1 ∈ e0.target ∧
      ‖e0.symm (heightCoordinates (nestedReferenceDiffeomorph d q)).1‖ ≤ 3 * rho ∧
      nestedReferenceDiffeomorph d q = heightCoordinates.symm
        ((heightCoordinates (nestedReferenceDiffeomorph d q)).1,
          U (heightCoordinates (nestedReferenceDiffeomorph d q)).1 + d)
    simp only [hshear]
    refine ⟨ht, hnormInv, ?_⟩
    apply heightCoordinates.injective
    rw [hshear, heightCoordinates.apply_symm_apply]
    change (v, w + ‖v‖ ^ 2 + v 0 / 32 + d) = (v, U v + d)
    rw [hwEq]
    congr 1
    dsimp only [U]
    ring
  refine ⟨ws, wm, hwslo, hwsup, hwsroot, hwmp, hwmh, hwmroot,
    rho, e0, e, hvs, hvm, hklo, hkhi, hmulo, hmax, hunique, hrho,
    hradHeight, hzero, hclosedSource, htargetD, he0, he0i, hquad, hfull,
    hlowerImage, rfl, heSource, heTarget, fun _ => rfl, fun _ => rfl,
    he, hei, heQuad, ?_⟩
  dsimp only
  intro d
  refine ⟨hwhole d, ?_⟩
  intro h hh
  change mu - rho ^ 2 - rho ^ 2 / 8 / 4 ≤ h ∧
    h ≤ mu - rho ^ 2 + rho ^ 2 / 8 / 4 at hh
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hgap0 : 0 < mu - h := by nlinarith only [hh.2, hrho2]
  have hgap2 : mu - h < 2 * rho ^ 2 := by nlinarith only [hh.1, hrho2]
  have hthreshold : mu - 9 * rho ^ 2 < h := by nlinarith only [hgap2, hrho2]
  have hroot0 : 0 ≤ Real.sqrt (mu - h) := Real.sqrt_nonneg _
  have hroot2 := Real.sq_sqrt hgap0.le
  have hrootlt : Real.sqrt (mu - h) < 3 * rho := by
    nlinarith only [hroot0, hroot2, hgap2, hrho, hrho2]
  have hsrc : closedBall (0 : E2) (Real.sqrt (mu - h)) ⊆ e.source := by
    rw [heSource]
    intro p hp
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans_lt hrootlt)
  have hpreimage (y : E3) (hy : y ∈ (nestedReferenceBallChart d).boundary)
      (hheight : h + d ≤ (heightCoordinates y).2) :
      (heightCoordinates y).1 ∈ e.target ∧
      e.symm (heightCoordinates y).1 ∈ closedBall (0 : E2) (Real.sqrt (mu - h)) ∧
      y = heightCoordinates.symm ((heightCoordinates y).1, U (heightCoordinates y).1 + d) := by
    obtain ⟨ht, _hn, hyEq⟩ := hwhole d y hy (by linarith only [hheight, hthreshold])
    have hvheight : h ≤ U (heightCoordinates y).1 := by
      have heq := congrArg (fun z : E3 => (heightCoordinates z).2) hyEq
      rw [heightCoordinates.apply_symm_apply] at heq
      linarith only [heq, hheight]
    have hq := hquad (e0.symm (heightCoordinates y).1) (e0.map_target ht)
    rw [e0.right_inv ht] at hq
    have hnormInv : ‖e0.symm (heightCoordinates y).1‖ ≤ Real.sqrt (mu - h) := by
      nlinarith only [hq, hvheight, hroot2, hroot0, norm_nonneg (e0.symm (heightCoordinates y).1)]
    have hp : e0.symm (heightCoordinates y).1 ∈ ball (0 : E2) (3 * rho) :=
      mem_ball_zero_iff.mpr (hnormInv.trans_lt hrootlt)
    refine ⟨?_, mem_closedBall_zero_iff.mpr hnormInv, hyEq⟩
    rw [heTarget]
    exact ⟨e0.symm (heightCoordinates y).1, hp, e0.right_inv ht⟩
  refine ⟨hgap0, hgap2, hsrc, fun y hy => (hpreimage y hy.1 hy.2).1, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hh⟩
    obtain ⟨ht, hp, hyEq⟩ := hpreimage y hy hh
    refine ⟨e.symm (heightCoordinates y).1, hp, ?_⟩
    change heightCoordinates.symm (e (e.symm (heightCoordinates y).1),
      U (e (e.symm (heightCoordinates y).1)) + d) = y
    rw [e.right_inv ht]
    exact hyEq.symm
  · rintro ⟨p, hp, rfl⟩
    have hpS := hsrc hp
    have hv : e p ∈ ball (0 : E2) 1 := htargetD (e0.map_source hpS.1)
    refine ⟨hgraphMem d (e p) hv, ?_⟩
    change h + d ≤ (heightCoordinates (heightCoordinates.symm (e p, U (e p) + d))).2
    rw [heightCoordinates.apply_symm_apply, heQuad p hpS]
    have hn := mem_closedBall_zero_iff.mp hp
    nlinarith only [hn, norm_nonneg p, hroot0, hroot2]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
