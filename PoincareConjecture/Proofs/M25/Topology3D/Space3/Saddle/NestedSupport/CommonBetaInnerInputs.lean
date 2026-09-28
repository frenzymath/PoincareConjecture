import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaPackets
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaInnerData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.ShortReturnRadialApproach
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ComparisonCircleAssembly
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonCapExteriorFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarCurveNormalChart
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

noncomputable section

private def innerSx : Fin 4 → ℝ := saddleNestedInnerSx
private def innerSy : Fin 4 → ℝ := saddleNestedInnerSy
private def innerEp : Fin 2 × Fin 2 ≃ Fin 4 := saddleNestedInnerEp
private def innerPort (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (i e : Fin 2) : E2 :=
  saddleNestedInnerPort J2 i e

set_option maxHeartbeats 1500000 in

set_option linter.unusedVariables false in

theorem exists_saddle_common_beta_inner_inputs
    (hP : PlanarSchoenfliesService)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h nu : ℝ) (hh : 0 < h) (hhnu : h < nu / 128)
    (hsmall : h < 1 / 1024) (inner : Fin 2)
    (alpha outerAlpha : Fin 2 → ℝ → E2)
    (Bi Bo : Fin 2 → BallNeighborhoodChart E2 E2)
    (EtaI EtaO : Fin 2 → Set E2)
    (hAlpha : ∀ j, ContDiffOn ℝ ∞ (alpha j) (Ioo (-nu) (1 + nu)))
    (hAlphaInj : ∀ j, InjOn (alpha j) (Ioo (-nu) (1 + nu)))
    (hAlphaReg : ∀ j t, t ∈ Ioo (-nu) (1 + nu) → deriv (alpha j) t ≠ 0)
    (hAlphaProper : ∀ j, alpha j '' Ioo (0 : ℝ) 1 ⊆
      (kappa '' closedBall (0 : E2) 1)ᶜ)
    (hAlphaInitial : ∀ j t, |t| < nu →
      alpha j t = kappa ((1 + t) • innerPort J2 inner 0))
    (hAlphaTerminal : ∀ j t, |t - 1| < nu →
      alpha j t = kappa ((2 - t) • innerPort J2 inner 1))
    (hOuter : ∀ j, ContDiffOn ℝ ∞ (outerAlpha j) (Ioo (-nu) (1 + nu)))
    (hOuterBoundary : ∀ j,
      (Bo j).boundary = outerAlpha j '' Icc (0 : ℝ) 1 ∪ EtaO j)
    (hInnerBoundary : ∀ j,
      (Bi j).boundary = alpha j '' Icc (0 : ℝ) 1 ∪ EtaI j)
    (hNested : ∀ j, (Bi j).closedRegion ⊆ (Bo j).inside)
    (S : CommonBetaInnerShortData kappa J2 h inner)
    (F : CommonBetaInnerFilledData kappa Bi J2 h inner)
    (hAnnular : ∀ j, (alpha j '' Icc (0 : ℝ) 1) ∩
      (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
      kappa '' (((fun r : ℝ => r • innerPort J2 inner 0) '' Icc 1 (1 + 32 * h)) ∪
        ((fun r : ℝ => r • innerPort J2 inner 1) '' Icc 1 (1 + 32 * h))))
    (hInner : ∀ j, kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
      |(J2 x).1| < (![1, -1] inner) * (J2 x).2} ⊆ (Bi j).inside)
    (hInnerClosed : ∀ j, kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
      |(J2 x).1| ≤ (![1, -1] inner) * (J2 x).2} ⊆ (Bi j).closedRegion) :
    ∃ I : Fin 2 → CommonBetaPacketInput,
      (∀ j, (I j).kappa = kappa ∧
        (I j).alpha = ![alpha j, S.beta] ∧
        (I j).l = 3 * h ∧ (I j).r = 1 - 3 * h ∧ (I j).eta = h / 256) ∧
      (∀ j, (I j).F =
        (kappa '' closedBall (0 : E2) 1) ∪
          (outerAlpha j '' Icc (0 : ℝ) 1) ∪
          (alpha j '' (Icc 0 (3 * h) ∪ Icc (1 - 3 * h) 1))) := by
  classical
  let sx : Fin 4 → ℝ := innerSx
  let sy : Fin 4 → ℝ := innerSy
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := innerEp
  let sign : Fin 2 → ℝ := ![1, -1]
  let port : Fin 4 → E2 := fun a => J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let K : Set E2 := kappa '' closedBall (0 : E2) 1
  let l : ℝ := 3 * h
  let r : ℝ := 1 - 3 * h
  let eta : ℝ := h / 256
  let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
  let Uarc : Set ℝ := Ioo (-eta) (1 + eta)
  let Gpar : Set ℝ := Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)
  let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
  let A : Fin 2 → Fin 2 → Fin 2 → ℝ → E2 :=
    fun j _ k => if k = 0 then alpha j else S.beta
  let v : E2 := J2.symm (1, 0)
  let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  have hnu : 0 < nu := by linarith
  have hUold : U ⊆ Ioo (-nu) (1 + nu) := by
    intro t ht; dsimp [U] at ht; constructor <;> linarith [ht.1, ht.2]
  have h01U : Icc (0 : ℝ) 1 ⊆ U := by
    intro t ht; dsimp [U]; constructor <;> linarith [ht.1, ht.2]
  have h01old : Icc (0 : ℝ) 1 ⊆ Ioo (-nu) (1 + nu) := h01U.trans hUold
  have hArcU : Uarc ⊆ U := by
    intro t ht
    have ht1 : -h / 256 < t := by
      simpa [Uarc, eta, div_eq_mul_inv] using ht.1
    have ht2 : t < 1 + h / 256 := by
      simpa [Uarc, eta, div_eq_mul_inv] using ht.2
    have hleft : -h / 8 < -h / 256 := by nlinarith [hh]
    have hright : 1 + h / 256 < 1 + h / 8 := by nlinarith [hh]
    simpa [U] using (show -h / 8 < t ∧ t < 1 + h / 8 from
      ⟨hleft.trans ht1, ht2.trans hright⟩)
  have hmid01 : Icc l r ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht; dsimp [l, r] at ht; constructor <;> linarith [ht.1, ht.2]
  have hmidClosed : Icc l r ⊆ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩
  have hTail01 : Tailpar ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    rcases ht with ht | ht <;> dsimp [l, r] at ht <;>
      constructor <;> linarith [ht.1, ht.2]
  have hnorm (x y : ℝ) : ‖J2.symm (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    simpa only [J2.apply_symm_apply] using (hJ2 (J2.symm (x, y))).symm
  have hport (a : Fin 4) : ‖port a‖ = 1 := by
    have hn := hnorm (sx a / Real.sqrt 2) (sy a / Real.sqrt 2)
    have hs : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by fin_cases a <;>
      norm_num [sx, sy, innerSx, innerSy, saddleNestedInnerSx, saddleNestedInnerSy]
    change ‖port a‖ ^ 2 = _ at hn
    rw [div_pow, div_pow, hs.1, hs.2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    nlinarith [norm_nonneg (port a)]
  have hinnerPort (i e : Fin 2) : ‖innerPort J2 i e‖ = 1 := by
    simpa [innerPort, saddleNestedInnerPort, innerSx, innerSy, innerEp,
      saddleNestedInnerSx, saddleNestedInnerSy, saddleNestedInnerEp, port, sx, sy, ep] using
      hport (ep (i, e))
  have hsrc {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kappa.source := hkappaSource (by
    simpa only [mem_closedBall, dist_zero_right] using hx)
  have hKsrc : closedBall (0 : E2) 1 ⊆ kappa.source := by
    intro x hx; apply hsrc
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    linarith
  have hKcompact : IsCompact K := by
    exact (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      (kappa.continuousOn.mono hKsrc)
  have hKpre : IsPreconnected K := (convex_closedBall (0 : E2) 1).isPreconnected.image
    kappa (kappa.continuousOn.mono hKsrc)
  have hBetaIn (j : Fin 2) : S.beta '' Icc (0 : ℝ) 1 ⊆ (Bi j).closedRegion := by
    rintro y ⟨t, ht, rfl⟩
    apply hInnerClosed j
    refine ⟨S.b t, ?_, ?_⟩
    · exact ⟨(S.hBetaRange ht).1, by linarith [(S.hBetaRange ht).2.1,
        (S.hBetaRange ht).1], (S.hBetaRange ht).2.2⟩
    · rw [S.hBetaDef]
      rfl
  have hGammaIn (j : Fin 2) : S.gamma '' Icc (0 : ℝ) 1 ⊆ (Bi j).closedRegion := by
    rintro y ⟨t, ht, rfl⟩
    apply hInnerClosed j
    refine ⟨S.g t, ?_, ?_⟩
    · exact ⟨by linarith [(S.hGammaRange ht).1, hh],
        by linarith [(S.hGammaRange ht).2.1], (S.hGammaRange ht).2.2⟩
    · rw [S.hGammaDef]
      rfl
  have hAlphaIn (j : Fin 2) : alpha j '' Icc (0 : ℝ) 1 ⊆ (Bi j).closedRegion := by
    intro x hx
    rw [← (Bi j).inside_union_boundary, hInnerBoundary j]
    exact Or.inr (Or.inl hx)
  have hOuterIn (j : Fin 2) : outerAlpha j '' Icc (0 : ℝ) 1 ⊆ (Bo j).closedRegion := by
    intro x hx
    rw [← (Bo j).inside_union_boundary, hOuterBoundary j]
    exact Or.inr (Or.inl hx)
  have hAdata (j i k : Fin 2) : ContDiffOn ℝ ∞ (A j i k) U ∧
      InjOn (A j i k) U ∧ ∀ t ∈ U, deriv (A j i k) t ≠ 0 := by
    by_cases hk : k = 0
    · simp only [A, if_pos hk]
      exact ⟨(hAlpha j).mono hUold, (hAlphaInj j).mono hUold,
        fun t ht => hAlphaReg j t (hUold ht)⟩
    · simp only [A, if_neg hk]
      exact ⟨S.hBetaData.1, S.hBetaData.2.1, S.hBetaData.2.2⟩
  have hGdata : ContDiffOn ℝ ∞ S.gamma U ∧ InjOn S.gamma U ∧
      ∀ t ∈ U, deriv S.gamma t ≠ 0 :=
    ⟨S.hGammaData.1, S.hGammaData.2.1, S.hGammaData.2.2⟩
  have hAL (j k : Fin 2) (t : ℝ) (ht : t ∈ U)
      (hlo : |t| < nu) (hhi : t ≤ 4 * h) : A j 0 k t =
      kappa ((1 + t) • port (ep (inner, 0))) := by
    by_cases hk : k = 0
    · simpa only [A, if_pos hk, port, sx, sy, ep, innerPort, saddleNestedInnerPort,
        innerSx, innerSy, innerEp, saddleNestedInnerSx, saddleNestedInnerSy,
        saddleNestedInnerEp]
        using hAlphaInitial j t hlo
    · simpa only [A, if_neg hk, port, sx, sy, ep, innerPort, saddleNestedInnerPort,
        innerSx, innerSy, innerEp, saddleNestedInnerSx, saddleNestedInnerSy,
        saddleNestedInnerEp]
        using (S.hGerms t ht).1 hhi
  have hAR (j k : Fin 2) (t : ℝ) (ht : t ∈ U)
      (hhi : |t - 1| < nu) (hlo : 1 - 4 * h ≤ t) : A j 0 k t =
      kappa ((2 - t) • port (ep (inner, 1))) := by
    by_cases hk : k = 0
    · simpa only [A, if_pos hk, port, sx, sy, ep, innerPort, saddleNestedInnerPort,
        innerSx, innerSy, innerEp, saddleNestedInnerSx, saddleNestedInnerSy,
        saddleNestedInnerEp]
        using hAlphaTerminal j t hhi
    · simpa only [A, if_neg hk, port, sx, sy, ep, innerPort, saddleNestedInnerPort,
        innerSx, innerSy, innerEp, saddleNestedInnerSx, saddleNestedInnerSy,
        saddleNestedInnerEp]
        using (S.hGerms t ht).2.1 hlo
  have hGR (j i k : Fin 2) (s : ℝ) (hs : |s| < h / 16) :
      S.gamma s = A j i k (r + s) := by
    have hb := abs_lt.mp hs
    have hsU : s ∈ U := by dsimp [U]; constructor <;> linarith [hb.1, hb.2]
    rw [(S.hGerms s hsU).2.2.1 (by linarith)]
    rw [hAR j k (r + s) (by dsimp [U, r]; constructor <;> linarith)
      (by rw [abs_lt]; dsimp [r]; constructor <;> linarith)
      (by dsimp [r]; linarith)]
    congr 2; dsimp [r]; ring
  have hGL (j i k : Fin 2) (s : ℝ) (hs : |s - 1| < h / 16) :
      S.gamma s = A j i k (l + s - 1) := by
    have hb := abs_lt.mp hs
    have hsU : s ∈ U := by dsimp [U]; constructor <;> linarith [hb.1, hb.2]
    rw [(S.hGerms s hsU).2.2.2 (by linarith)]
    rw [hAL j k (l + s - 1) (by dsimp [U, l]; constructor <;> linarith)
      (by rw [abs_lt]; dsimp [l]; constructor <;> linarith)
      (by dsimp [l]; linarith)]
    congr 2; dsimp [l]; ring
  have hAnnPar (j : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (x : E2) (hx : 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h)
      (heq : alpha j t = kappa x) : t = ‖x‖ - 1 ∨ t = 2 - ‖x‖ := by
    have hm : alpha j t ∈ (alpha j '' Icc (0 : ℝ) 1) ∩
        (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) :=
      ⟨⟨t, ht, rfl⟩, ⟨x, hx, heq.symm⟩⟩
    rw [hAnnular j] at hm
    rcases hm with ⟨y, hy, hky⟩
    rcases hy with ⟨R, hR, rfl⟩ | ⟨R, hR, rfl⟩
    · have hRsrc : (R • innerPort J2 inner 0) ∈ kappa.source := by
        apply hsrc
        have hR0 : 0 ≤ R := by linarith [hR.1]
        change ‖R • innerPort J2 inner 0‖ ≤ 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR0, hinnerPort]
        linarith [hR.2, hsmall]
      have hxR := kappa.injOn (hsrc (by linarith [hx.2])) hRsrc
        (heq.symm.trans hky.symm)
      have hn : ‖x‖ = R := by
        have hR0 : 0 ≤ R := by linarith [hR.1]
        rw [hxR, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR0, hinnerPort]
        simp
      have hp : |R - 1| < nu := by rw [abs_lt]; constructor <;> linarith [hR.1, hR.2]
      left; rw [hn]
      exact hAlphaInj j (h01old ht) ⟨by linarith [hR.1], by linarith [hR.2]⟩
        (hky.symm.trans (by
          convert (hAlphaInitial j (R - 1) hp).symm using 1
          congr 2
          ring))
    · have hRsrc : (R • innerPort J2 inner 1) ∈ kappa.source := by
        apply hsrc
        have hR0 : 0 ≤ R := by linarith [hR.1]
        change ‖R • innerPort J2 inner 1‖ ≤ 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR0, hinnerPort]
        linarith [hR.2, hsmall]
      have hxR := kappa.injOn (hsrc (by linarith [hx.2])) hRsrc
        (heq.symm.trans hky.symm)
      have hn : ‖x‖ = R := by
        have hR0 : 0 ≤ R := by linarith [hR.1]
        rw [hxR, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR0, hinnerPort]
        simp
      have hp : |(2 - R) - 1| < nu := by rw [abs_lt]; constructor <;> linarith [hR.1, hR.2]
      right; rw [hn]
      exact hAlphaInj j (h01old ht) ⟨by linarith [hR.2], by linarith [hR.1]⟩
        (hky.symm.trans (by
          convert (hAlphaTerminal j (2 - R) hp).symm using 1
          congr 2
          ring))
  have hMeet (j i k : Fin 2) :
      (S.gamma '' Icc (0 : ℝ) 1) ∩ (A j i k '' Icc l r) =
        {A j i k l, A j i k r} := by
    by_cases hk : k = 0
    · apply Subset.antisymm
      · rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
        have hgx := S.hGammaRange hs
        change 1 + h ≤ ‖S.g s‖ ∧ ‖S.g s‖ ≤ 1 + 3 * h ∧
          |(J2 (S.g s)).1| ≤ (![1, -1] inner) * (J2 (S.g s)).2 at hgx
        have ha : alpha j t = kappa (S.g s) := by
          rw [S.hGammaDef, Function.comp_apply] at heq
          simpa only [A, if_pos hk] using heq
        rcases hAnnPar j t ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩ (S.g s)
          ⟨by linarith [hgx.1], by linarith [hgx.2.1]⟩ ha with hp | hp
        · have htval : t = l := by
            dsimp [l]
            nlinarith [hp, hgx.2.1, ht.1]
          left
          simp [← heq, htval]
        · have htval : t = r := by
            dsimp [r]
            nlinarith [hp, hgx.2.1, ht.2]
          right
          simp [← heq, htval]
      · intro x hx
        rcases hx with rfl | hx
        · refine ⟨⟨1, by constructor <;> norm_num, ?_⟩, ⟨l, ⟨le_rfl, ?_⟩, rfl⟩⟩
          · simpa only [add_sub_cancel_right] using
              hGL j i k 1 (by rw [abs_lt]; constructor <;> linarith [hh])
          · dsimp [l, r]; linarith
        · subst x
          refine ⟨⟨0, by constructor <;> norm_num, ?_⟩, ⟨r, ⟨?_, le_rfl⟩, rfl⟩⟩
          · simpa only [add_zero] using hGR j i k 0
              (by rw [abs_lt]; constructor <;> linarith [hh])
          · dsimp [l, r]; linarith
    · simpa only [A, if_neg hk] using S.hJoins.2.2.1
  obtain ⟨a, bpar, ham, hbm, habDer, hassemble⟩ :=
    exists_saddle_comparison_circle_assembly J2 hJ2 h hh hsmall
  obtain ⟨Q, C, Z, hv, hQs, hQt, hqform, hqinv, hq, hqi, hqInj, hqReg,
    hqImage, hqEnds, hcForm, hc, hcCommon, hcQ, hcImages, hZs, hZt,
    hZform, hZinv, hZ, hZi, hJcZ, hZDc, hcZ⟩ :=
      hassemble A (fun _ => S.gamma) (fun j i k => hAdata j i k) (fun _ => hGdata)
        (fun j i k s hs => hGR j i k s hs) (fun j i k s hs => hGL j i k s hs)
        hMeet
  let c : Fin 2 → Fin 2 → UnitCircle → E2 := fun j i => C j 0 i
  let Delta : Fin 2 → Fin 2 → Set E2 := fun _ _ => S.gamma '' Icc (0 : ℝ) 1
  have hDelta (j i : Fin 2) : Delta j i = c j 0 '' Dc := by
    simpa [Delta, c, Dc] using (hcImages j 0 0).1.symm
  have hRange (j i : Fin 2) : range (c j i) = Delta j i ∪
      (A j 0 i '' Icc l r) := by
    simpa [c, Delta, l, r] using (hcImages j 0 i).2.1
  have hRangeB (j i : Fin 2) : range (c j i) ⊆ (Bi j).closedRegion := by
    rw [hRange j i]
    apply union_subset
    · exact hGammaIn j
    · intro x hx
      by_cases hi : i = 0
      · rcases hx with ⟨t, ht, hxt⟩
        apply hAlphaIn j
        exact ⟨t, hmidClosed ht, by simpa [A, hi] using hxt⟩
      · rcases hx with ⟨t, ht, hxt⟩
        apply hBetaIn j
        exact ⟨t, hmidClosed ht, by simpa [A, hi] using hxt⟩
  have hDeltaK (j i : Fin 2) : Delta j i ⊆ Kᶜ := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    apply S.hGammaProper
    exact ⟨t, h01U ht, rfl⟩
  have hRangeK (j i : Fin 2) : Disjoint (range (c j i)) K := by
    rw [hRange j i]
    apply Set.disjoint_left.mpr
    intro x hx hxK
    rcases hx with hx | hx
    · exact hDeltaK j i hx hxK
    · by_cases hi : i = 0
      · rcases hx with ⟨t, ht, hxt⟩
        have hxin : x ∈ alpha j '' Ioo (0 : ℝ) 1 :=
          ⟨t, hmid01 ht, by simpa [A, hi] using hxt⟩
        exact (hAlphaProper j hxin) hxK
      · rcases hx with ⟨t, ht, hxt⟩
        have hxin : x ∈ S.beta '' Ioo (0 : ℝ) 1 :=
          ⟨t, hmid01 ht, by simpa [A, hi] using hxt⟩
        exact (S.hBetaProper hxin) hxK
  have hOther (j : Fin 2) : outerAlpha j '' Icc (0 : ℝ) 1 ⊆
      (Bi j).closedRegionᶜ := by
    intro x hx hxi
    exact Set.disjoint_left.mp (Bo j).inside_disjoint_boundary
      (hNested j hxi) (by rw [hOuterBoundary j]; exact Or.inl hx)
  have hTailBoundary (j : Fin 2) : alpha j '' Tailpar ⊆ (Bi j).boundary := by
    intro x hx
    rw [hInnerBoundary j]
    exact Or.inl ((image_mono hTail01) hx)
  have hRetTail (j i : Fin 2) :
      (A j 0 i '' Icc l r) ∩ (alpha j '' Tailpar) ⊆ Delta j i := by
    by_cases hi : i = 0
    · intro x hx
      rcases hx with ⟨⟨t, ht, htx⟩, ⟨s, hs, hsx⟩⟩
      have htx' : alpha j t = x := by simpa [A, hi] using htx
      have hst : s = t := hAlphaInj j (h01old (hTail01 hs))
        (h01old (hmidClosed ht)) (hsx.trans htx'.symm)
      subst s
      have hlU : l ∈ U := by
        dsimp [U, l]
        constructor <;> linarith [hh, hsmall]
      have hrU : r ∈ U := by
        dsimp [U, r]
        constructor <;> linarith [hh, hsmall]
      have hBetaAlphaL : S.beta l = alpha j l := by
        rw [(S.hGerms l hlU).1 (by dsimp [l]; linarith)]
        exact (hAlphaInitial j l (by rw [abs_lt]; constructor <;> linarith [hhnu])).symm
      have hBetaAlphaR : S.beta r = alpha j r := by
        rw [(S.hGerms r hrU).2.1 (by dsimp [r]; linarith)]
        exact (hAlphaTerminal j r (by rw [abs_lt]; constructor <;> linarith [hhnu])).symm
      rcases hs with hs | hs
      · have he : t = l := le_antisymm hs.2 ht.1
        subst t
        have hjoin : S.gamma 1 = S.beta l := by
          simpa [l] using S.hJoins.2.1
        exact ⟨1, ⟨zero_le_one, le_rfl⟩,
          hjoin.trans (hBetaAlphaL.trans htx')⟩
      · have he : t = r := le_antisymm ht.2 hs.1
        subst t
        have hjoin : S.gamma 0 = S.beta r := by
          simpa [r] using S.hJoins.1
        exact ⟨0, ⟨le_rfl, zero_le_one⟩,
          hjoin.trans (hBetaAlphaR.trans htx')⟩
    · intro x hx
      rcases hx with ⟨⟨t, ht, htx⟩, ⟨s, hs, hsx⟩⟩
      have htx' : S.beta t = x := by simpa [A, hi] using htx
      have hBetaEq : S.beta t = alpha j s := by
        exact htx'.trans hsx.symm
      have hBetaPhys : S.beta t = kappa (S.b t) := by
        rw [S.hBetaDef, Function.comp_apply]
      have ha : alpha j s = kappa (S.b t) := hBetaEq.symm.trans hBetaPhys
      have hbx := S.hBetaRange (hmidClosed ht)
      rcases hAnnPar j s (hTail01 hs) (S.b t)
        ⟨hbx.1, by linarith [hbx.2.1]⟩ ha with hp | hp
      · rcases hs with hs | hs
        · have hnormUpper : ‖S.b t‖ ≤ 1 + 3 * h := by
            dsimp [l] at hs
            linarith [hp, hs.2]
          have hnormEq : ‖S.b t‖ = 1 + 3 * h :=
            le_antisymm hnormUpper (S.hBetaCut t ht).1
          rcases (S.hBetaCut t ht).2.mp hnormEq with htend | htend
          · subst t
            have hjoin : S.gamma 1 = S.beta l := by
              simpa [l] using S.hJoins.2.1
            exact ⟨1, ⟨zero_le_one, le_rfl⟩,
              hjoin.trans (by simpa [l] using htx')⟩
          · subst t
            have hjoin : S.gamma 0 = S.beta r := by
              simpa [r] using S.hJoins.1
            exact ⟨0, ⟨le_rfl, zero_le_one⟩,
              hjoin.trans (by simpa [r] using htx')⟩
        · exfalso
          dsimp [r] at hs
          have hnormLower : 2 - 3 * h ≤ ‖S.b t‖ := by
            linarith [hp, hs.1]
          nlinarith [hbx.2.1, hsmall]
      · rcases hs with hs | hs
        · exfalso
          dsimp [l] at hs
          have hnormLower : 2 - 3 * h ≤ ‖S.b t‖ := by
            linarith [hp, hs.2]
          nlinarith [hbx.2.1, hsmall]
        · have hnormUpper : ‖S.b t‖ ≤ 1 + 3 * h := by
            dsimp [r] at hs
            linarith [hp, hs.1]
          have hnormEq : ‖S.b t‖ = 1 + 3 * h :=
            le_antisymm hnormUpper (S.hBetaCut t ht).1
          rcases (S.hBetaCut t ht).2.mp hnormEq with htend | htend
          · subst t
            have hjoin : S.gamma 1 = S.beta l := by
              simpa [l] using S.hJoins.2.1
            exact ⟨1, ⟨zero_le_one, le_rfl⟩,
              hjoin.trans (by simpa [l] using htx')⟩
          · subst t
            have hjoin : S.gamma 0 = S.beta r := by
              simpa [r] using S.hJoins.1
            exact ⟨0, ⟨le_rfl, zero_le_one⟩,
              hjoin.trans (by simpa [r] using htx')⟩
  have hMeetCap (j i : Fin 2) : range (c j i) ∩ (alpha j '' Tailpar) ⊆ Delta j i := by
    intro x hx
    rw [hRange j i] at hx
    rcases hx with ⟨hxRange, hxTail⟩
    rcases hxRange with hxDelta | hxMiddle
    · exact hxDelta
    · exact hRetTail j i ⟨hxMiddle, hxTail⟩
  let O : Fin 2 → Set E2 := fun j => outerAlpha j '' Icc (0 : ℝ) 1
  let T : Fin 2 → Set E2 := fun j => alpha j '' Tailpar
  let Fj : Fin 2 → Set E2 := fun j => K ∪ O j ∪ T j
  have hOcompact (j : Fin 2) : IsCompact (O j) := by
    exact isCompact_Icc.image_of_continuousOn
      ((hOuter j).continuousOn.mono h01old)
  have hTcompact (j : Fin 2) : IsCompact (T j) := by
    exact (isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      ((hAlpha j).continuousOn.mono (hTail01.trans h01old))
  have hFclosed (j : Fin 2) : IsClosed (Fj j) := by
    exact (hKcompact.union (hOcompact j)).union (hTcompact j) |>.isClosed
  have hFdecomp (j i : Fin 2) : Fj j = K ∪ O j ∪ T j := by
    rfl
  have hKsubF (j : Fin 2) : K ⊆ Fj j := by
    intro x hx
    exact Or.inl (Or.inl hx)
  have hTailSubF (j : Fin 2) : T j ⊆ Fj j := by
    intro x hx
    exact Or.inr hx
  have hPortSphere (i e : Fin 2) : innerPort J2 i e ∈ sphere (0 : E2) 1 := by
    exact mem_sphere_zero_iff_norm.mpr (hinnerPort i e)
  have hZeroU : (0 : ℝ) ∈ U := by
    dsimp [U]
    constructor <;> linarith [hh]
  have hOneU : (1 : ℝ) ∈ U := by
    dsimp [U]
    constructor <;> linarith [hh, hsmall]
  have hGparU : Gpar ⊆ U := by
    intro t ht
    rcases ht with ht | ht
    · change t ∈ Ioo (-eta) (l + eta) at ht
      rcases ht with ⟨ht1, ht2⟩
      dsimp [eta, l] at ht1 ht2
      dsimp [U, l, eta]
      constructor <;> nlinarith [ht1, ht2, hh, hsmall]
    · change t ∈ Ioo (r - eta) (1 + eta) at ht
      rcases ht with ⟨ht1, ht2⟩
      dsimp [eta, r] at ht1 ht2
      dsimp [U, r, eta]
      constructor <;> nlinarith [ht1, ht2, hh, hsmall]
  have hNsourcePacket : Ioo (-eta) (1 + eta) ×ˢ ({0} : Set ℝ) ⊆ S.N.source := by
    intro p hp
    rcases p with ⟨t, z⟩
    have hz : z = 0 := by simpa using hp.2
    rcases hp.1 with ⟨ht1, ht2⟩
    subst z
    apply S.hNsource
    refine ⟨?_, ?_⟩
    · dsimp [eta]
      dsimp [eta] at ht1 ht2
      constructor <;> linarith [ht1, ht2, hh]
    · exact ⟨by linarith [S.hw], S.hw.le⟩
  have hNzeroPacket (t : ℝ) (ht : t ∈ Ioo (-eta) (1 + eta)) :
      S.N (t, 0) = S.gamma t := by
    rw [S.hNform (t, 0) (hNsourcePacket ⟨ht, rfl⟩)]
    simp
  have hBetaAlphaL (j : Fin 2) : S.beta l = alpha j l := by
    have hlt : l ∈ U := by
      dsimp [U, l]
      constructor <;> linarith [hh, hsmall]
    rw [(S.hGerms l hlt).1 (by dsimp [l]; linarith)]
    exact (hAlphaInitial j l (by rw [abs_lt]; constructor <;> linarith [hhnu])).symm
  have hBetaAlphaR (j : Fin 2) : S.beta r = alpha j r := by
    have hrt : r ∈ U := by
      dsimp [U, r]
      constructor <;> linarith [hh, hsmall]
    rw [(S.hGerms r hrt).2.1 (by dsimp [r]; linarith)]
    exact (hAlphaTerminal j r (by rw [abs_lt]; constructor <;> linarith [hhnu])).symm
  have hPacketEnds (j : Fin 2) :
      alpha j 0 ∈ kappa '' sphere (0 : E2) 1 ∧
        alpha j 1 ∈ kappa '' sphere (0 : E2) 1 := by
    constructor
    · rw [hAlphaInitial j 0 (by simpa using hnu)]
      exact ⟨innerPort J2 inner 0, hPortSphere inner 0, by simp⟩
    · rw [hAlphaTerminal j 1 (by simpa using hnu)]
      exact ⟨innerPort J2 inner 1, hPortSphere inner 1,
        by norm_num [innerPort, saddleNestedInnerPort]⟩
  have hBetaEnds :
      S.beta 0 ∈ kappa '' sphere (0 : E2) 1 ∧
        S.beta 1 ∈ kappa '' sphere (0 : E2) 1 := by
    have h0 := (S.hGerms 0 hZeroU).1 (by linarith)
    have h1 := (S.hGerms 1 hOneU).2.1 (by linarith)
    constructor
    · rw [h0]
      exact ⟨innerPort J2 inner 0, hPortSphere inner 0,
        by norm_num [innerPort, saddleNestedInnerPort]⟩
    · rw [h1]
      exact ⟨innerPort J2 inner 1, hPortSphere inner 1,
        by norm_num [innerPort, saddleNestedInnerPort]⟩
  have hnu128 : h * 128 < nu :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < 128)).mp hhnu
  have hGermsPacket (j : Fin 2) :
      EqOn (alpha j) S.beta Gpar := by
    intro t ht
    rcases ht with ht | ht
    · rcases ht with ⟨htL, htR⟩
      have hU := hGparU (Or.inl ⟨htL, htR⟩)
      have ha : |t| < nu := by
        rw [abs_lt]
        dsimp [l, eta] at htL htR
        constructor <;> nlinarith [hnu128, hh]
      have hb : t ≤ 4 * h := by
        dsimp [l, eta] at htR
        nlinarith [htR, hh]
      have hleft := hAlphaInitial j t ha
      have hright := (S.hGerms t hU).1 hb
      simpa [innerPort, saddleNestedInnerPort] using hleft.trans hright.symm
    · rcases ht with ⟨htL, htR⟩
      have hU := hGparU (Or.inr ⟨htL, htR⟩)
      have ha : |t - 1| < nu := by
        rw [abs_lt]
        dsimp [r, eta] at htL htR
        constructor <;> nlinarith [hnu128, hh]
      have hb : 1 - 4 * h ≤ t := by
        dsimp [r, eta] at htL
        nlinarith [htL, hh]
      have hleft := hAlphaTerminal j t ha
      have hright := (S.hGerms t hU).2.1 hb
      simpa [innerPort, saddleNestedInnerPort] using hleft.trans hright.symm
  have hMid : kappa (S.g (1 / 2)) =
      kappa (J2.symm (0, (![1, -1] inner) * (1 + h))) := by
    simpa [S.hGammaDef, Function.comp_apply] using S.hJoins.2.2.2
  have hBetaBounds (t : ℝ) (ht : t ∈ Icc l r) :
      1 + 3 * h ≤ ‖S.b t‖ ∧ ‖S.b t‖ ≤ 1 + 6 * h := by
    have hb := S.hBetaRange (hmidClosed ht)
    exact ⟨(S.hBetaCut t ht).1, by linarith [hb.2.1]⟩
  have hGammaBounds (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      1 + h ≤ ‖S.g t‖ ∧ ‖S.g t‖ ≤ 1 + 3 * h := by
    have hg := S.hGammaRange ht
    exact ⟨hg.1, hg.2.1⟩
  obtain ⟨hpathC, hpath0, hpathPre, hpathGamma, hpathBeta,
      hpathAlpha, hpathEnd, hpathEndK⟩ :=
    saddle_nested_short_return_radial_approach kappa hkappaSource J2 hJ2 h hh hsmall inner
      alpha S.b S.g hBetaBounds hGammaBounds hMid hAnnular
  let path : ℝ → E2 := fun t =>
    kappa (J2.symm (0, (![1, -1] inner) * (1 + h - t)))
  have hpathGamma' : Disjoint (path '' Ioc (0 : ℝ) h)
      (S.gamma '' Icc (0 : ℝ) 1) := by
    simpa [path, S.hGammaDef, Function.comp_apply] using hpathGamma
  have hpathMiddle (j i : Fin 2) :
      Disjoint (path '' Ioc (0 : ℝ) h) (A j 0 i '' Icc l r) := by
    by_cases hi : i = 0
    · simpa [A, hi] using (hpathAlpha j).mono_right (image_mono hmidClosed)
    · simpa [A, hi, S.hBetaDef, Function.comp_apply, l, r] using hpathBeta
  have hpathBoundary (j i : Fin 2) :
      Disjoint (path '' Ioc (0 : ℝ) h) (range (c j i)) := by
    rw [hRange j i]
    exact hpathGamma'.union_right (hpathMiddle j i)
  have hpathEndDelta (j i : Fin 2) : path h ∉ Delta j i := by
    apply Set.disjoint_left.mp hpathGamma'
    exact ⟨h, ⟨hh, le_rfl⟩, rfl⟩
  have hPathF (j i : Fin 2) : path h ∈ Fj j := by
    have hk : path h ∈ K := by simpa [path, K] using hpathEndK
    exact Or.inl (Or.inl hk)
  have hOutside (j i : Fin 2) : ∃ x ∈ K, x ∉ (Bi j).closedRegion := by
    refine ⟨kappa 0, ?_, ?_⟩
    · exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), rfl⟩
    · apply F.hLong j
      exact ⟨0, F.hZero j, rfl⟩
  have hpath0' : path 0 = S.gamma (1 / 2) := by
    simpa [path, S.hGammaDef, Function.comp_apply] using hpath0
  let I : Fin 2 → CommonBetaPacketInput := fun j => {
    kappa := kappa
    hkappaSource := hKsrc
    hkappa := hkappa
    hkappaInv := hkappaInv
    alpha := ![alpha j, S.beta]
    l := l
    r := r
    eta := eta
    F := Fj j
    v := v
    B := fun _ => Bi j
    c := fun i => c j i
    K := fun _ => K
    O := fun _ => O j
    T := fun _ => T j
    Delta := fun i => Delta j i
    q := Q
    gamma := S.gamma
    Z := Z
    N0 := S.N
    path := path
    d := h
    hl := by dsimp [l]; linarith
    hlr := by dsimp [l, r]; linarith
    hr := by dsimp [r]; linarith
    heta := by dsimp [eta]; linarith
    hetal := by dsimp [eta, l]; linarith
    hetar := by dsimp [eta, r]; linarith
    hgap := by dsimp [eta, l, r]; linarith
    hF := hFclosed j
    hFdecomp := fun i => hFdecomp j i
    hKF := hKsubF j
    hAlpha := by
      intro i
      fin_cases i
      · simpa [Uarc] using (hAlpha j).mono (hArcU.trans hUold)
      · simpa [Uarc] using S.hBetaData.1.mono hArcU
    hAlphaInj := by
      intro i
      fin_cases i
      · simpa [Uarc] using (hAlphaInj j).mono (hArcU.trans hUold)
      · simpa [Uarc] using S.hBetaData.2.1.mono hArcU
    hAlphaReg := by
      intro i t ht
      fin_cases i
      · exact hAlphaReg j t (hUold (hArcU (by simpa [Uarc] using ht)))
      · exact S.hBetaData.2.2 t (hArcU (by simpa [Uarc] using ht))
    hEnds := by
      intro i
      fin_cases i
      · exact hPacketEnds j
      · exact hBetaEnds
    hProper := by
      intro i
      fin_cases i
      · exact hAlphaProper j
      · exact S.hBetaProper
    hGerms := hGermsPacket j
    hTails := by
      intro x hx
      rcases hx with ⟨t, ht, htx⟩
      exact hTailSubF j ⟨t, ht, htx⟩
    hv := hv
    hc := fun i => hc j 0 i
    hK := fun _ => hKpre
    hOutside := fun i => hOutside j i
    hCurve := fun i => hRangeB j i
    hCurveK := fun i => hRangeK j i
    hcK := fun i => hRangeK j i
    hOther := by
      intro i
      simpa [O] using hOther j
    hTail := by
      intro i
      simpa [T] using hTailBoundary j
    hMeet := fun i => hMeetCap j i
    hDelta := fun i => hDelta j i
    hCCommon := by
      intro p hp
      exact (hcCommon j 0 0 hp).trans (hcCommon j 0 1 hp).symm
    hZtarget := hZt
    hJcZ := hJcZ
    hZ := hZ
    hZi := hZi
    hCommon := fun i p hp => hcZ j 0 i p hp
    hN0source := hNsourcePacket
    hN0 := S.hN
    hN0i := S.hNi
    hN0zero := hNzeroPacket
    hpathC := hpathC
    hpath0 := hpath0'
    hd := hh
    hpathPreconn := hpathPre
    hpathBoundary := fun i => hpathBoundary j i
    hpathEnd := fun i => ⟨hPathF j i, hpathEndDelta j i⟩
    hq := hq
    hqInj := hqInj
    hqReg := hqReg
    hqImage := hqImage
    hqEnds := hqEnds
    hTracks := by
      intro i t ht
      fin_cases i
      · simpa [c, A, l, r, eta] using hcQ j 0 0 t ht
      · simpa [c, A, l, r, eta] using hcQ j 0 1 t ht }
  refine ⟨I, ?_, ?_⟩
  · intro j
    simp [I, l, r, eta]
  · intro j
    simp [I, K, Fj, O, T, Tailpar, image_union, l, r]

end

end PoincareConjecture.M25.Topology3D
