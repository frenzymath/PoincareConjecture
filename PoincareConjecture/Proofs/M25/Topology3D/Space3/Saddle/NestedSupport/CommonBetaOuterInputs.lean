import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaPackets
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorOuterFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorOuterAnnulus
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.RaisedReturnRadialAvoidance
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ComparisonCircleAssembly
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarCurveNormalChart

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1500000 in

theorem exists_saddle_common_beta_outer_input
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h nu : ℝ) (hh : 0 < h) (hhnu : h < nu / 128)
    (hsmall : h < 1 / 1024) (inner : Fin 2)
    (mu : Fin 2 → ℝ) (hmu : ∀ j, 0 < mu j)
    (hmuSmall : ∀ j, mu j ≤ 1 / 128)
    (reconnect : Fin 2 → E2 → E2)
    (hReconnectNorm : ∀ j x, ‖reconnect j x‖ = ‖x‖) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let outer : Fin 2 := raisedReturnOther inner
    let K : Set E2 := kappa '' closedBall (0 : E2) 1
    ∀ (alpha : Fin 2 → ℝ → E2) (beta : ℝ → E2)
      (Bi Bo : Fin 2 → BallNeighborhoodChart E2 E2) (Eta : Fin 2 → Set E2),
      (∀ j, ContDiffOn ℝ ∞ (alpha j) (Ioo (-nu) (1 + nu))) →
      (∀ j, InjOn (alpha j) (Ioo (-nu) (1 + nu))) →
      (∀ j t, t ∈ Ioo (-nu) (1 + nu) → deriv (alpha j) t ≠ 0) →
      (∀ j, alpha j '' Ioo (0 : ℝ) 1 ⊆ Kᶜ) →
      (∀ j t, |t| < nu → alpha j t = kappa ((1 + t) • port (ep (outer, 0)))) →
      (∀ j t, |t - 1| < nu → alpha j t = kappa ((2 - t) • port (ep (outer, 1)))) →
      ContDiffOn ℝ ∞ beta (Ioo (-h / 8) (1 + h / 8)) →
      beta 0 = kappa (port (ep (inner, 0))) →
      MapsTo beta (Icc (0 : ℝ) 1)
        (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 6 * h ∧
          |(J2 x).1| ≤ raisedReturnSign inner * (J2 x).2}) →
      (∀ j, (Bo j).boundary = alpha j '' Icc (0 : ℝ) 1 ∪ Eta j) →
      (∀ j, Eta j ⊆ K) →
      (∀ j, (alpha j '' Icc (0 : ℝ) 1) ∩
          (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
        kappa ''
          (((fun r : ℝ => r • port (ep (outer, 0))) '' Icc 1 (1 + 32 * h)) ∪
          ((fun r : ℝ => r • port (ep (outer, 1))) '' Icc 1 (1 + 32 * h)))) →
      (∀ j, kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
          |(J2 x).1| < raisedReturnSign inner * (J2 x).2} ⊆ (Bi j).inside) →
      (∀ j, kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
          |(J2 x).1| ≤ raisedReturnSign inner * (J2 x).2} ⊆ (Bi j).closedRegion) →
      (∀ j, (Bi j).closedRegion ⊆ (Bo j).inside) →
      (∀ j, kappa '' (reconnect j '' {x : E2 | ‖x‖ ≤ 1 ∧
          Real.sqrt ((J2 x).1 ^ 2 + mu j) <
            raisedReturnSign outer * (J2 x).2}) ⊆ (Bo j).closedRegionᶜ) →
      ∃ I : CommonBetaPacketInput,
        I.kappa = kappa ∧ I.alpha = alpha ∧ I.l = 3 * h ∧
        I.r = 1 - 3 * h ∧ I.eta = h / 256 ∧
        I.F = (K ∪ beta '' Icc (0 : ℝ) 1) ∪
          alpha 0 '' (Icc (0 : ℝ) (3 * h) ∪ Icc (1 - 3 * h) 1) ∪
          alpha 1 '' (Icc (0 : ℝ) (3 * h) ∪ Icc (1 - 3 * h) 1) := by
  classical
  dsimp only
  intro alpha beta Bi Bo Eta hAlpha hAlphaInj hAlphaReg hProper hInitial hTerminal
    hBeta hBetaStart hBetaRange hBoundary hEta hAnnular hInner hInnerClosed hNested hShort
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a =>
    J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let outer : Fin 2 := raisedReturnOther inner
  let l : ℝ := 3 * h
  let r : ℝ := 1 - 3 * h
  let eta : ℝ := h / 256
  let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
  let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
  let K : Set E2 := kappa '' closedBall (0 : E2) 1
  let Kstar : Set E2 := K ∪ beta '' Icc (0 : ℝ) 1
  let T : Fin 2 → Set E2 := fun j => alpha j '' Tailpar
  let Fouter : Set E2 := Kstar ∪ T 0 ∪ T 1
  let gamma : ℝ → E2 := raisedReturnPhysicalCurve kappa J2 h inner
  let Delta : Set E2 := gamma '' Icc (0 : ℝ) 1
  let v : E2 := J2.symm (1, 0)
  let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  have hnu : 0 < nu := by linarith
  have h01old : Icc (0 : ℝ) 1 ⊆ Ioo (-nu) (1 + nu) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hUold : U ⊆ Ioo (-nu) (1 + nu) := by
    intro t ht
    dsimp [U] at ht
    constructor <;> linarith [ht.1, ht.2]
  have h01U : Icc (0 : ℝ) 1 ⊆ U := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hArcU : Ioo (-eta) (1 + eta) ⊆ U := by
    intro t ht
    dsimp [eta, U] at *
    constructor <;> linarith [ht.1, ht.2]
  have hTail01 : Tailpar ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    rcases ht with ht | ht <;> dsimp [l, r] at ht <;>
      constructor <;> linarith [ht.1, ht.2]
  have hmid01 : Icc l r ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    dsimp [l, r] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hmidClosed : Icc l r ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩
  have hKsource : closedBall (0 : E2) 1 ⊆ kappa.source :=
    (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hkappaSource
  have hportN (a : Fin 4) : ‖port a‖ = 1 := by
    have hn := hJ2 (port a)
    have hs : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by
      fin_cases a <;> norm_num [sx, sy]
    simp only [port, J2.apply_symm_apply, div_pow, hs.1, hs.2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    nlinarith [norm_nonneg (port a)]
  have hPoleN (i : Fin 2) : ‖J2.symm (0, raisedReturnSign i)‖ = 1 := by
    have hn := hJ2 (J2.symm (0, raisedReturnSign i))
    simp only [J2.apply_symm_apply, raisedReturnSign_sq,
      zero_pow (by norm_num : 2 ≠ 0), zero_add] at hn
    nlinarith [norm_nonneg (J2.symm (0, raisedReturnSign i))]
  have hKcompact : IsCompact K := (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
    (kappa.continuousOn.mono hKsource)
  have hBetaCompact : IsCompact (beta '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn (hBeta.continuousOn.mono h01U)
  have hTcompact (j : Fin 2) : IsCompact (T j) :=
    (isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      ((hAlpha j).continuousOn.mono (hTail01.trans h01old))
  have hFclosed : IsClosed Fouter :=
    (((hKcompact.union hBetaCompact).union (hTcompact 0)).union (hTcompact 1)).isClosed
  have hBeta0K : beta 0 ∈ K := by
    rw [hBetaStart]
    exact ⟨port (ep (inner, 0)), mem_closedBall_zero_iff.mpr (hportN _).le, rfl⟩
  have hKpre : IsPreconnected K := (convex_closedBall (0 : E2) 1).isPreconnected.image
    kappa (kappa.continuousOn.mono hKsource)
  have hBetaPre : IsPreconnected (beta '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image beta (hBeta.continuousOn.mono h01U)
  have hKstarPre : IsPreconnected Kstar :=
    hKpre.union (beta 0) hBeta0K ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ hBetaPre
  have hOutside (j : Fin 2) : ∃ x ∈ Kstar, x ∉ (Bo j).closedRegion := by
    let x : E2 := J2.symm (0, raisedReturnSign outer)
    have hx : x ∈ {z : E2 | ‖z‖ ≤ 1 ∧
        Real.sqrt ((J2 z).1 ^ 2 + mu j) < raisedReturnSign outer * (J2 z).2} := by
      refine ⟨(hPoleN outer).le, ?_⟩
      simp only [x, J2.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0), zero_add,
        ← pow_two, raisedReturnSign_sq]
      nlinarith [Real.sq_sqrt (hmu j).le, Real.sqrt_nonneg (mu j), hmuSmall j]
    refine ⟨kappa (reconnect j x), Or.inl ?_, hShort j ⟨reconnect j x, ⟨x, hx, rfl⟩, rfl⟩⟩
    exact ⟨reconnect j x, by
      rw [mem_closedBall_zero_iff, hReconnectNorm]
      exact (hPoleN outer).le, rfl⟩
  have hBetaIn (j : Fin 2) : beta '' Icc (0 : ℝ) 1 ⊆ (Bi j).closedRegion := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨x, hx, hxb⟩ := hBetaRange ht
    exact hInnerClosed j ⟨x, ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩, hxb⟩
  obtain ⟨g, gam, hgDef, hgamDef, _hgSmooth, hgammaSmooth, _hgInj, hgammaInj,
      hRegular, _hGammaEq, hGSource, _hBounds, _hMid, _hLeft, _hRight, _hBetaRange,
      hGammaBeta⟩ := exists_saddle_nested_raised_long_return
    kappa hkappaSource hkappa hkappaInv J2 hJ2 h hh hsmall inner beta hBetaRange
  subst g
  subst gam
  have hGerms (j : Fin 2) := saddle_nested_raised_long_return_original_germs
    kappa J2 h nu hh hhnu hsmall inner (alpha j) (hInitial j) (hTerminal j)
  have hSide (j : Fin 2) := saddle_nested_raised_long_return_outer_filling
    kappa hkappaSource J2 hJ2 h nu hh hhnu hsmall inner (alpha j) (Bi j) (Bo j)
    (Eta j) (hAlphaInj j) (hInitial j) (hTerminal j) (hBoundary j) (hEta j)
    (hAnnular j) (hInner j) (hNested j)
  let A : Fin 2 → Fin 2 → Fin 2 → ℝ → E2 := fun j _ _ => alpha j
  have hA (j i k : Fin 2) : ContDiffOn ℝ ∞ (A j i k) U ∧
      InjOn (A j i k) U ∧ ∀ t ∈ U, deriv (A j i k) t ≠ 0 :=
    ⟨(hAlpha j).mono hUold, (hAlphaInj j).mono hUold,
      fun t ht => hAlphaReg j t (hUold ht)⟩
  obtain ⟨_a, _b, _ham, _hbm, _habDer, hassemble⟩ :=
    exists_saddle_comparison_circle_assembly J2 hJ2 h hh hsmall
  obtain ⟨Q, C, Z, hv, _hQs, _hQt, _hqForm, _hqInv, hq, _hqi, hqInj, hqReg,
      hqImage, hqEnds, _hcForm, hc, hcCommon, hcQ, hcImages, _hZs, hZt,
      _hZform, _hZinv, hZ, hZi, hJcZ, _hZDc, hcZ⟩ :=
    hassemble A (fun _ => gamma) hA
      (fun _ => ⟨hgammaSmooth, hgammaInj, fun t ht => (hRegular t ht).2⟩)
      (fun j _ _ => (hGerms j).1) (fun j _ _ => (hGerms j).2.1)
      (fun j _ _ => (hSide j).2.2)
  let c : Fin 2 → UnitCircle → E2 := fun j => C j 0 0
  have hCap (j : Fin 2) : c j '' Dc = Delta := (hcImages j 0 0).1
  have hRange (j : Fin 2) : range (c j) = Delta ∪ alpha j '' Icc l r :=
    (hcImages j 0 0).2.1
  have hAlphaBoundary (j : Fin 2) : alpha j '' Icc (0 : ℝ) 1 ⊆ (Bo j).boundary := by
    rw [hBoundary j]
    exact subset_union_left
  have hAlphaClosed (j : Fin 2) : alpha j '' Icc (0 : ℝ) 1 ⊆ (Bo j).closedRegion := by
    intro x hx
    rw [← (Bo j).inside_union_boundary]
    exact Or.inr (hAlphaBoundary j hx)
  have hRangeClosed (j : Fin 2) : range (c j) ⊆ (Bo j).closedRegion := by
    rw [hRange j]
    exact union_subset (hSide j).2.1 ((image_mono hmidClosed).trans (hAlphaClosed j))
  have hDeltaK : Disjoint Delta K := by
    apply disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ ⟨x, hx, hxg⟩
    have heq := kappa.injOn (hKsource hx) (hGSource t (h01U ht)).1 hxg
    have hn : ‖raisedReturnPlanarCurve J2 h inner t‖ ≤ 1 := by
      rw [← heq]
      exact mem_closedBall_zero_iff.mp hx
    exact (not_le_of_gt (hGSource t (h01U ht)).2.1) hn
  have hRangeK (j : Fin 2) : Disjoint (range (c j)) K := by
    apply disjoint_left.mpr
    intro x hx hxK
    rw [hRange j] at hx
    rcases hx with hx | hx
    · exact disjoint_left.mp hDeltaK hx hxK
    · exact hProper j ((image_mono hmid01) hx) hxK
  have hRangeKstar (j : Fin 2) : Disjoint (range (c j)) Kstar := by
    apply disjoint_left.mpr
    intro x hx hxK
    rcases hxK with hxK | hxBeta
    · exact disjoint_left.mp (hRangeK j) hx hxK
    · rw [hRange j] at hx
      rcases hx with hx | hx
      · exact disjoint_left.mp hGammaBeta hx hxBeta
      · exact disjoint_left.mp (Bo j).inside_disjoint_boundary
          (hNested j (hBetaIn j hxBeta)) (hAlphaBoundary j ((image_mono hmidClosed) hx))
  have hCuts (j : Fin 2) : alpha j l ∈ Delta ∧ alpha j r ∈ Delta := by
    constructor
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      simpa [l] using (hGerms j).2.2.2 1 ⟨by linarith, le_rfl⟩
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      simpa [r] using (hGerms j).2.2.1 0 ⟨le_rfl, hh.le⟩
  have hMeet (j : Fin 2) : range (c j) ∩ T j ⊆ Delta := by
    rintro x ⟨hx, ⟨s, hs, hsx⟩⟩
    rw [hRange j] at hx
    rcases hx with hx | ⟨t, ht, htx⟩
    · exact hx
    · have hst : s = t := (hAlphaInj j) (h01old (hTail01 hs))
        (h01old (hmidClosed ht)) (hsx.trans htx.symm)
      subst s
      rcases hs with hs | hs
      · have he : t = l := le_antisymm hs.2 ht.1
        rw [← htx, he]
        exact (hCuts j).1
      · have he : t = r := le_antisymm ht.2 hs.1
        rw [← htx, he]
        exact (hCuts j).2
  have hTailPoint (j : Fin 2) (t : ℝ) (ht : t ∈ Tailpar) : alpha j t = alpha 0 t := by
    rcases ht with ht | ht
    · have ha : |t| < nu := by
        apply abs_lt.mpr
        dsimp [l] at ht
        constructor <;> linarith [ht.1, ht.2]
      rw [hInitial j t ha, hInitial 0 t ha]
    · have ha : |t - 1| < nu := by
        apply abs_lt.mpr
        dsimp [r] at ht
        constructor <;> linarith [ht.1, ht.2]
      rw [hTerminal j t ha, hTerminal 0 t ha]
  have hTailEq (j : Fin 2) : T j = T 0 := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hTailPoint j t ht).symm⟩
    · rintro x ⟨t, ht, rfl⟩
      exact ⟨t, ht, hTailPoint j t ht⟩
  have hFdecomp (j : Fin 2) : Fouter = Kstar ∪ (∅ : Set E2) ∪ T j := by
    change (Kstar ∪ T 0) ∪ T 1 = (Kstar ∪ ∅) ∪ T j
    rw [hTailEq 1, hTailEq j, union_empty, union_assoc, union_self]
  have hCommonGerms : EqOn (alpha 0) (alpha 1)
      (Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)) := by
    intro t ht
    rcases ht with ht | ht
    · have ha : |t| < nu := by
        apply abs_lt.mpr
        dsimp [eta, l] at ht
        constructor <;> linarith [ht.1, ht.2]
      rw [hInitial 0 t ha, hInitial 1 t ha]
    · have ha : |t - 1| < nu := by
        apply abs_lt.mpr
        dsimp [eta, r] at ht
        constructor <;> linarith [ht.1, ht.2]
      rw [hTerminal 0 t ha, hTerminal 1 t ha]
  have hAlphaEnds (j : Fin 2) : alpha j 0 ∈ kappa '' sphere (0 : E2) 1 ∧
      alpha j 1 ∈ kappa '' sphere (0 : E2) 1 := by
    constructor
    · rw [hInitial j 0 (by simpa using hnu)]
      refine ⟨port (ep (outer, 0)), mem_sphere_zero_iff_norm.mpr (hportN _), ?_⟩
      simp [port, ep, outer, sx, sy]
    · rw [hTerminal j 1 (by simpa using hnu)]
      refine ⟨port (ep (outer, 1)), mem_sphere_zero_iff_norm.mpr (hportN _), ?_⟩
      norm_num [port, ep, outer, sx, sy]
  have hNormalImage : gamma '' Icc (-h / 16) (1 + h / 16) ⊆ kappa.target := by
    rintro y ⟨t, ht, rfl⟩
    exact kappa.map_source (hGSource t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1
  obtain ⟨w0, N0, hw0, hNrect, _hNsub, _hNt, hN, hNi, hNform⟩ :=
    exists_saddle_planar_curve_normal_chart J2 gamma (-h / 8) (1 + h / 8)
      (-h / 16) (1 + h / 16) (by linarith) (by linarith) (by linarith)
      hgammaSmooth hgammaInj (fun t ht => (hRegular t ht).2)
      kappa.target kappa.open_target hNormalImage
  have hNsource : Ioo (-eta) (1 + eta) ×ˢ ({0} : Set ℝ) ⊆ N0.source := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    apply hNrect
    dsimp [eta] at ht
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith, hw0.le⟩⟩
  have hNzero (t : ℝ) (ht : t ∈ Ioo (-eta) (1 + eta)) : N0 (t, 0) = gamma t := by
    rw [hNform (t, 0) (hNsource ⟨ht, rfl⟩), zero_smul, add_zero]
  let path : ℝ → E2 := fun t =>
    kappa (J2.symm (0, raisedReturnSign inner * (1 + 10 * h - t)))
  obtain ⟨hpathC, hpath0, hpathPre, hpathGamma, hpathEnd⟩ :=
    saddle_nested_raised_return_radial_avoidance kappa hkappaSource J2 hJ2 h hh hsmall inner
  have hpathAlpha (j : Fin 2) :
      Disjoint (path '' Ioc (0 : ℝ) (10 * h)) (alpha j '' Icc (0 : ℝ) 1) := by
    apply (saddle_nested_outer_arc_avoids_inner_pole kappa hkappaSource J2 hJ2
      h hh hsmall inner (alpha j) (hAnnular j)).mono_left
    rintro x ⟨t, ht, rfl⟩
    exact ⟨J2.symm (0, raisedReturnSign inner * (1 + 10 * h - t)),
      ⟨1 + 10 * h - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩, rfl⟩
  have hpathBoundary (j : Fin 2) :
      Disjoint (path '' Ioc (0 : ℝ) (10 * h)) (range (c j)) := by
    rw [hRange j]
    exact hpathGamma.union_right ((hpathAlpha j).mono_right (image_mono hmidClosed))
  have hpathEndK : path (10 * h) ∈ K := by
    change (fun t => kappa (J2.symm (0, raisedReturnSign inner *
      (1 + 10 * h - t)))) (10 * h) ∈ K
    rw [hpathEnd]
    exact ⟨J2.symm (0, raisedReturnSign inner),
      mem_closedBall_zero_iff.mpr (hPoleN inner).le, rfl⟩
  have hpathEndDelta : path (10 * h) ∉ Delta :=
    disjoint_left.mp hpathGamma ⟨10 * h, ⟨by linarith, le_rfl⟩, rfl⟩
  let I : CommonBetaPacketInput := {
    kappa := kappa, hkappaSource := hKsource, hkappa := hkappa, hkappaInv := hkappaInv
    alpha := alpha, l := l, r := r, eta := eta, F := Fouter, v := v
    B := Bo, c := c, K := fun _ => Kstar, O := fun _ => ∅, T := T
    Delta := fun _ => Delta, q := Q, gamma := gamma, Z := Z, N0 := N0
    path := path, d := 10 * h
    hl := by dsimp [l]; linarith
    hlr := by dsimp [l, r]; linarith
    hr := by dsimp [r]; linarith
    heta := by dsimp [eta]; linarith
    hetal := by dsimp [eta, l]; linarith
    hetar := by dsimp [eta, r]; linarith
    hgap := by dsimp [eta, l, r]; linarith
    hF := hFclosed, hFdecomp := hFdecomp
    hKF := fun _ hx => Or.inl (Or.inl (Or.inl hx))
    hAlpha := fun j => (hAlpha j).mono (hArcU.trans hUold)
    hAlphaInj := fun j => (hAlphaInj j).mono (hArcU.trans hUold)
    hAlphaReg := fun j t ht => hAlphaReg j t (hUold (hArcU ht))
    hEnds := hAlphaEnds, hProper := hProper, hGerms := hCommonGerms
    hTails := fun _ hx => Or.inl (Or.inr hx)
    hv := hv, hc := fun j => hc j 0 0, hK := fun _ => hKstarPre
    hOutside := hOutside, hCurve := hRangeClosed, hCurveK := hRangeKstar
    hcK := hRangeK, hOther := fun _ => empty_subset _
    hTail := fun j => (image_mono hTail01).trans (hAlphaBoundary j)
    hMeet := hMeet, hDelta := fun _ => (hCap 0).symm
    hCCommon := fun _ hp => (hcCommon 1 0 0 hp).symm
    hZtarget := hZt, hJcZ := hJcZ, hZ := hZ, hZi := hZi
    hCommon := fun j => hcZ j 0 0
    hN0source := hNsource, hN0 := hN, hN0i := hNi, hN0zero := hNzero
    hpathC := hpathC, hpath0 := hpath0, hd := by linarith
    hpathPreconn := hpathPre, hpathBoundary := hpathBoundary
    hpathEnd := fun _ => ⟨Or.inl (Or.inl (Or.inl hpathEndK)), hpathEndDelta⟩
    hq := hq, hqInj := hqInj, hqReg := hqReg, hqImage := hqImage, hqEnds := hqEnds
    hTracks := fun j => hcQ j 0 0 }
  exact ⟨I, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.M25.Topology3D
