import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedAnnularBuffer
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ShortSectorTemplates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ComparisonCircleAssembly
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonCapExteriorFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonExteriorHalfStrip
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic








set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

set_option linter.unusedVariables false in



theorem exists_nonnested_common_cap_inputs
    (hP : PlanarSchoenfliesService)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : Fin 2 → ℝ) (hmu : ∀ j, 0 < mu j)
    (hmuSmall : ∀ j, mu j ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      fun j => Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi
        hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let other : Fin 2 → Fin 2 := Equiv.swap (0 : Fin 2) 1
    let K := kappa '' closedBall (0 : E2) 1
    let Kboundary := kappa '' sphere (0 : E2) 1
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Fin 2 → Set E2 := fun j i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu j)}
    let Eta : Fin 2 → Fin 2 → Set E2 := fun j i =>
      kappa '' ((F j 1) '' Z j i)
    ∀ (nu : ℝ) (hnu : 0 < nu) (hnuSmall : nu < 1 / 16)
      (alpha : Fin 2 → Fin 2 → ℝ → E2)
      (hAlpha : ∀ j i,
        ContDiffOn ℝ ∞ (alpha j i) (Ioo (-nu) (1 + nu)))
      (hAlphaInj : ∀ j i, Set.InjOn (alpha j i) (Ioo (-nu) (1 + nu)))
      (hAlphaReg : ∀ j i, ∀ t ∈ Ioo (-nu) (1 + nu), deriv (alpha j i) t ≠ 0)
      (hPair : ∀ j, Disjoint (alpha j 0 '' Icc (0 : ℝ) 1)
        (alpha j 1 '' Icc (0 : ℝ) 1))
      (hProper : ∀ j i, alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ)
      (hInitial : ∀ j i t, |t| < nu →
        alpha j i t = kappa ((1 + t) • port (ep (i, 0))))
      (hTerminal : ∀ j i t, |t - 1| < nu →
        alpha j i t = kappa ((2 - t) • port (ep (i, 1))))
      (B : Fin 2 → Fin 2 → BallNeighborhoodChart E2 E2)
      (hBoundary : ∀ j i,
        (B j i).boundary = (alpha j i '' Icc (0 : ℝ) 1) ∪ Eta j i)
      (hCase : ∀ j, Disjoint (B j 0).closedRegion (B j 1).closedRegion),
      ∃ (h l r eta : ℝ) (beta : Fin 2 → ℝ → E2)
        (c : Fin 2 → Fin 2 → Fin 2 → UnitCircle → E2)
        (q : ℝ → UnitCircle)
        (W : Fin 2 → Fin 2 → Fin 2 → Set E2)
        (Uc : Set UnitCircle) (w : ℝ)
        (N : Fin 2 → OpenPartialHomeomorph (UnitCircle × ℝ) E2),
      let v : E2 := J2.symm (1, 0)
      let Uarc : Set ℝ := Ioo (-eta) (1 + eta)
      let Gpar : Set ℝ := Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)
      let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
      let Umid : Set ℝ := Ioo (l - eta) (r + eta)
      let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
      let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
      let Ac : Set UnitCircle := {p | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
      let Delta : Fin 2 → Set E2 := fun i => c 0 i 0 '' Dc
      let A : Fin 2 → Fin 2 → Fin 2 → ℝ → E2 :=
        fun j i k => if k = 0 then alpha j i else beta i
      let Protected : Fin 2 → Fin 2 → Set E2 := fun j i =>
        K ∪ (alpha j (other i) '' Icc (0 : ℝ) 1) ∪
          (beta (other i) '' Icc (0 : ℝ) 1) ∪ (alpha j i '' Tailpar)
      0 < h ∧ h < nu / 128 ∧ h < 1 / 1024 ∧
      l = 3 * h ∧ r = 1 - 3 * h ∧
      0 < eta ∧ eta < h / 8 ∧
      0 < l ∧ l < r ∧ r < 1 ∧ eta < l ∧ r + eta < 1 ∧ l + eta < r - eta ∧
      ‖v‖ = 1 ∧
      (∀ j i, IsClosed (Protected j i) ∧ K ⊆ Protected j i ∧
        alpha j i '' Tailpar ⊆ Protected j i) ∧
      (∀ j i k,
        ContDiffOn ℝ ∞ (A j i k) Uarc ∧ Set.InjOn (A j i k) Uarc ∧
        (∀ t ∈ Uarc, deriv (A j i k) t ≠ 0) ∧
        A j i k 0 ∈ Kboundary ∧ A j i k 1 ∈ Kboundary ∧
        A j i k '' Ioo (0 : ℝ) 1 ⊆ Kᶜ) ∧
      (∀ j i, Set.EqOn (alpha j i) (beta i) Gpar ∧
        beta i '' Icc (0 : ℝ) 1 ⊆ (B j i).closedRegion) ∧
      Disjoint (beta 0 '' Icc (0 : ℝ) 1) (beta 1 '' Icc (0 : ℝ) 1) ∧
      (∀ j i k, IsPlanarEmbedding (c j i k)) ∧
      (∀ j i k, Set.EqOn (c j i k) (c 0 i 0) Jc) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ q Umid ∧ Set.InjOn q Umid ∧
      (∀ t ∈ Umid, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) q t)) ∧
      q '' Icc l r = {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ ≤ (3 / 4 : ℝ)} ∧
      ({q l, q r} : Set UnitCircle) =
        {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ = (3 / 4 : ℝ)} ∧
      (∀ j i k, ∀ t ∈ Umid, c j i k (q t) = A j i k t) ∧
      (∀ j i k,
        range (c j i k) = Delta i ∪ (A j i k '' Icc l r) ∧
        Delta i ∩ (A j i k '' Icc l r) = {A j i k l, A j i k r} ∧
        Disjoint (range (c j i k)) K ∧
        range (c j i k) ∩ Protected j i ⊆ Delta i) ∧
      (∀ j i k,
        IsOpen (W j i k) ∧ IsConnected (W j i k) ∧
        ¬ Bornology.IsBounded (W j i k) ∧
        Disjoint (W j i k) (range (c j i k)) ∧
        Protected j i \ Delta i ⊆ W j i k) ∧
      IsOpen Uc ∧ Ac ⊆ Uc ∧ Uc ⊆ Jc ∧ 0 < w ∧
      (∀ i,
        Uc ×ˢ Icc (-w) w ⊆ (N i).source ∧
        ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ (N i) (N i).source ∧
        ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (N i).symm (N i).target ∧
        (∀ p ∈ Uc, N i (p, 0) = c 0 i 0 p) ∧
        ∀ j k, (N i) '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ W j i k) := by
  classical
  dsimp only
  intro nu hnu hnuSmall alpha hAlpha hAlphaInj hAlphaReg hPair hProper hInitial hTerminal B
      hBoundary hCase
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a => J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let other : Fin 2 → Fin 2 := Equiv.swap (0 : Fin 2) 1
  let sign : Fin 2 → ℝ := ![1, -1]
  let K := kappa '' closedBall (0 : E2) 1
  let Kboundary := kappa '' sphere (0 : E2) 1
  change ∀ j i, alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ at hProper
  change ∀ j i t, |t| < nu → alpha j i t = kappa ((1 + t) • port (ep (i, 0))) at hInitial
  change ∀ j i t, |t - 1| < nu → alpha j i t = kappa ((2 - t) • port (ep (i, 1))) at hTerminal
  obtain ⟨h, hh, hhnu, hhsmall, hside, hann, _, hcone⟩ :=
    exists_saddle_nonnested_annular_buffer kappa hkappaSource J2 hJ2 mu hmu hmuSmall
      chi hchi hchiBounds hchiSupport hchiOne nu hnu hnuSmall alpha hAlpha hProper
      hInitial hTerminal B hBoundary hCase
  let sigma : ℝ → ℝ := Real.smoothTransition
  let rb : ℝ → ℝ := fun t => 1 + 5 * h + (t - 5 * h) * (1 - sigma ((t - 4 * h) / (2 * h))) + (1
      - t - 5 * h) * (1 - sigma ((1 - t - 4 * h) / (2 * h)))
  let ab : ℝ → ℝ := fun t => Real.pi / 4 + (Real.pi / 2) * sigma ((t - 4 * h) / (1 - 8 * h))
  let rg : ℝ → ℝ := fun t => 1 + h + (2 * h - t) * (1 - sigma ((t - h) / h)) + (2 * h - (1 - t))
      * (1 - sigma ((1 - t - h) / h))
  let ag : ℝ → ℝ := fun t => 3 * Real.pi / 4 - (Real.pi / 2) * sigma ((t - h) / (1 - 2 * h))
  let bn : Fin 2 → ℝ → E2 := fun i t => J2.symm (sign i * rb t * Real.cos (ab t), sign i * rb t
      * Real.sin (ab t))
  let gn : Fin 2 → ℝ → E2 := fun i t => J2.symm (sign i * rg t * Real.cos (ag t), sign i * rg t
      * Real.sin (ag t))
  let beta : Fin 2 → ℝ → E2 := fun i => kappa ∘ bn i
  let gamma : Fin 2 → ℝ → E2 := fun i => kappa ∘ gn i
  let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
  let l : ℝ := 3 * h
  let r : ℝ := 1 - 3 * h
  let eta : ℝ := h / 256
  let Uarc : Set ℝ := Ioo (-eta) (1 + eta)
  let Gpar : Set ℝ := Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)
  let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
  let Umid : Set ℝ := Ioo (l - eta) (r + eta)
  let A : Fin 2 → Fin 2 → Fin 2 → ℝ → E2 := fun j i k => if k = 0 then alpha j i else beta i
  obtain ⟨w0, N0, hw0, hnSmooth, hnorms, hregular, hgerms, hsectors, hproperT, hjoins,
    hbetaPair, hgammaOther, hN0⟩ := exists_saddle_short_sector_templates kappa hkappaSource
        hkappa hkappaInv J2 hJ2 h hh hhsmall
  change ∀ i t, t ∈ U →
    (t ≤ 4 * h → beta i t = kappa ((1 + t) • port (ep (i, 0)))) ∧
    (1 - 4 * h ≤ t → beta i t = kappa ((2 - t) • port (ep (i, 1)))) ∧
    (t ≤ h → gamma i t = kappa ((1 + 3 * h - t) • port (ep (i, 1)))) ∧
    (1 - h ≤ t → gamma i t = kappa ((1 + 3 * h + t - 1) • port (ep (i, 0))))
    at hgerms
  have hsrc {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kappa.source := hkappaSource (by simpa only
      [mem_closedBall, dist_zero_right] using hx)
  have hUold : U ⊆ Ioo (-nu) (1 + nu) := by intro t ht; dsimp [U] at ht; constructor <;>
      linarith [ht.1, ht.2]
  have h01U : Icc (0 : ℝ) 1 ⊆ U := by intro t ht; dsimp [U]; constructor <;> linarith [ht.1, ht.2]
  have h01old : Icc (0 : ℝ) 1 ⊆ Ioo (-nu) (1 + nu) := h01U.trans hUold
  have hmid01 : Icc l r ⊆ Ioo (0 : ℝ) 1 := by intro t ht; dsimp [l, r] at ht; constructor <;>
      linarith [ht.1, ht.2]
  have hmidU : Icc l r ⊆ U := fun t ht => h01U ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩
  have hTail01 : Tailpar ⊆ Icc (0 : ℝ) 1 := by intro t ht; rcases ht with ht | ht <;> dsimp [l,
      r] at ht <;> constructor <;> linarith [ht.1, ht.2]
  have hArcU : Uarc ⊆ U := by intro t ht; dsimp [Uarc, U, eta] at *; constructor <;> linarith
      [ht.1, ht.2]
  have hnorm (x y : ℝ) : ‖J2.symm (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by simpa only
      [J2.apply_symm_apply] using (hJ2 (J2.symm (x, y))).symm
  have hport (a : Fin 4) : ‖port a‖ = 1 := by
    have hn := hnorm (sx a / Real.sqrt 2) (sy a / Real.sqrt 2)
    have hs : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by fin_cases a <;> norm_num [sx, sy]
    change ‖port a‖ ^ 2 = _ at hn
    rw [div_pow, div_pow, hs.1, hs.2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    nlinarith [norm_nonneg (port a)]
  have hportR (a : Fin 4) (R : ℝ) (hR : 0 ≤ R) : ‖R • port a‖ = R := by rw [norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hR, hport, mul_one]
  have hbnSrc (i : Fin 2) (t : ℝ) (ht : t ∈ U) : bn i t ∈ kappa.source := by
    apply hsrc
    rw [(hnorms i t ht).1]
    exact (hnorms i t ht).2.2.1.le
  have hgnSrc (i : Fin 2) (t : ℝ) (ht : t ∈ U) : gn i t ∈ kappa.source := by
    apply hsrc
    rw [(hnorms i t ht).2.2.2.1]
    exact (hnorms i t ht).2.2.2.2.2.le
  have hbetaIn (j i : Fin 2) : beta i '' Icc (0 : ℝ) 1 ⊆ (B j i).closedRegion := by
    rintro _ ⟨t, ht, rfl⟩; apply hcone j i; refine ⟨bn i t, ?_, rfl⟩
    exact ⟨((hsectors i).1 ht).1, by linarith [((hsectors i).1 ht).2.1], ((hsectors i).1 ht).2.2⟩
  have hgammaIn (j i : Fin 2) : gamma i '' Icc (0 : ℝ) 1 ⊆ (B j i).closedRegion := by
    rintro _ ⟨t, ht, rfl⟩; apply hcone j i; refine ⟨gn i t, ?_, rfl⟩
    exact ⟨by linarith [((hsectors i).2 ht).1], by linarith [((hsectors i).2 ht).2.1],
        ((hsectors i).2 ht).2.2⟩
  have hAlphaIn (j i : Fin 2) : alpha j i '' Icc (0 : ℝ) 1 ⊆ (B j i).closedRegion := by
    intro x hx; rw [← (B j i).inside_union_boundary]; right; rw [hBoundary j i]; exact Or.inl hx
  have hAdata (j i k : Fin 2) : ContDiffOn ℝ ∞ (A j i k) U ∧ InjOn (A j i k) U ∧ ∀ t ∈ U, deriv
      (A j i k) t ≠ 0 := by
    by_cases hk : k = 0
    · simp only [A, if_pos hk]; exact ⟨(hAlpha j i).mono hUold, (hAlphaInj j i).mono hUold, fun
        t ht => hAlphaReg j i t (hUold ht)⟩
    · simp only [A, if_neg hk]; exact ⟨(hregular i).1, (hregular i).2.1, (hregular i).2.2.1⟩
  have hGammaData (i : Fin 2) : ContDiffOn ℝ ∞ (gamma i) U ∧ InjOn (gamma i) U ∧ ∀ t ∈ U, deriv
      (gamma i) t ≠ 0 :=
    ⟨(hregular i).2.2.2.1, (hregular i).2.2.2.2.1, (hregular i).2.2.2.2.2⟩
  have hAL (j i k : Fin 2) (t : ℝ) (ht : t ∈ U) (hlo : |t| < nu) (hhi : t ≤ 4 * h) : A j i k t =
      kappa ((1 + t) • port (ep (i, 0))) := by
    by_cases hk : k = 0
    · simpa only [A, if_pos hk] using hInitial j i t hlo
    · simpa only [A, if_neg hk] using (hgerms i t ht).1 hhi
  have hAR (j i k : Fin 2) (t : ℝ) (ht : t ∈ U) (hhi : |t - 1| < nu) (hlo : 1 - 4 * h ≤ t) : A j
      i k t = kappa ((2 - t) • port (ep (i, 1))) := by
    by_cases hk : k = 0
    · simpa only [A, if_pos hk] using hTerminal j i t hhi
    · simpa only [A, if_neg hk] using (hgerms i t ht).2.1 hlo
  have hGR (j i k : Fin 2) (s : ℝ) (hs : |s| < h / 16) : gamma i s = A j i k (r + s) := by
    have hb := abs_lt.mp hs
    have hsU : s ∈ U := by
      change -h / 8 < s ∧ s < 1 + h / 8
      constructor <;> linarith [hb.1, hb.2]
    rw [(hgerms i s hsU).2.2.1 (by linarith)]
    rw [hAR j i k (r + s) (by dsimp [U, r]; constructor <;> linarith)
      (by rw [abs_lt]; dsimp [r]; constructor <;> linarith) (by dsimp [r]; linarith)]
    congr 2; dsimp [r]; ring
  have hGL (j i k : Fin 2) (s : ℝ) (hs : |s - 1| < h / 16) : gamma i s = A j i k (l + s - 1) := by
    have hb := abs_lt.mp hs
    have hsU : s ∈ U := by
      change -h / 8 < s ∧ s < 1 + h / 8
      constructor <;> linarith [hb.1, hb.2]
    rw [(hgerms i s hsU).2.2.2 (by linarith)]
    rw [hAL j i k (l + s - 1) (by dsimp [U, l]; constructor <;> linarith)
      (by rw [abs_lt]; dsimp [l]; constructor <;> linarith) (by dsimp [l]; linarith)]
    congr 2; dsimp [l]; ring
  have hEnds (j i k : Fin 2) : gamma i 0 = A j i k r ∧ gamma i 1 = A j i k l := by
    constructor
    · simpa only [add_zero] using hGR j i k 0 (by simpa using (show 0 < h / 16 by positivity))
    · simpa only [sub_self, add_sub_cancel_right] using hGL j i k 1 (by simpa using (show 0 < h
        / 16 by positivity))

  have hAnnPar (j i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E2)
      (hx : 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h) (heq : alpha j i t = kappa x) :
      t = ‖x‖ - 1 ∨ t = 2 - ‖x‖ := by
    have hm : alpha j i t ∈ (alpha j i '' Icc (0 : ℝ) 1) ∩
        (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) := ⟨⟨t, ht, rfl⟩, ⟨x, hx, heq.symm⟩⟩
    rw [hann j i] at hm
    rcases hm with ⟨y, hy, hky⟩
    rcases hy with ⟨R, hR, rfl⟩ | ⟨R, hR, rfl⟩
    · have hxR := kappa.injOn (hsrc (by linarith [hx.2]))
        (hsrc (by rw [hportR _ R (by linarith [hR.1])]; linarith [hR.2])) (heq.symm.trans hky.symm)
      have hn : ‖x‖ = R := by rw [hxR, hportR _ R (by linarith [hR.1])]
      have hp : |R - 1| < nu := by rw [abs_lt]; constructor <;> linarith [hR.1, hR.2]
      have hg : alpha j i (R - 1) = kappa (R • port (ep (i, 0))) := by
        rw [hInitial j i _ hp]
        congr 2
        ring
      left
      rw [hn]
      exact hAlphaInj j i (h01old ht) ⟨by linarith [hR.1], by linarith [hR.2]⟩
        (hky.symm.trans hg.symm)
    · have hxR := kappa.injOn (hsrc (by linarith [hx.2]))
        (hsrc (by rw [hportR _ R (by linarith [hR.1])]; linarith [hR.2])) (heq.symm.trans hky.symm)
      have hn : ‖x‖ = R := by rw [hxR, hportR _ R (by linarith [hR.1])]
      have hp : |(2 - R) - 1| < nu := by rw [abs_lt]; constructor <;> linarith [hR.1, hR.2]
      have hg : alpha j i (2 - R) = kappa (R • port (ep (i, 1))) := by
        rw [hTerminal j i _ hp]
        congr 2
        ring
      right
      rw [hn]
      exact hAlphaInj j i (h01old ht) ⟨by linarith [hR.2], by linarith [hR.1]⟩
        (hky.symm.trans hg.symm)
  have hMeet (j i k : Fin 2) : (gamma i '' Icc (0 : ℝ) 1) ∩ (A j i k '' Icc l r) = {A j i k l, A
      j i k r} := by
    by_cases hk : k = 0
    · apply Subset.antisymm
      · rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
        have hn := (hsectors i).2 hs
        have ha : alpha j i t = kappa (gn i s) := by simpa only [A, if_pos hk, gamma,
            comp_apply] using heq
        have hp := hAnnPar j i t ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩ (gn i s) ⟨by linarith
            [hn.1], by linarith [hn.2.1]⟩ ha
        have ht' : t = l ∨ t = r := by
          rcases hp with hp | hp
          · left
            dsimp [l, r] at ht ⊢
            linarith [ht.1, hn.2.1]
          · right
            dsimp [l, r] at ht ⊢
            linarith [ht.2, hn.2.1]
        rcases ht' with rfl | rfl
        · exact Or.inl heq.symm
        · exact Or.inr heq.symm
      · intro x hx; rcases hx with rfl | hx
        · refine ⟨⟨1, by constructor <;> norm_num, (hEnds j i k).2⟩, ⟨l, ⟨le_rfl, ?_⟩, rfl⟩⟩
          dsimp [l, r]
          linarith
        · rw [mem_singleton_iff] at hx; subst x
          refine ⟨⟨0, by constructor <;> norm_num, (hEnds j i k).1⟩, ⟨r, ⟨?_, le_rfl⟩, rfl⟩⟩
          dsimp [l, r]
          linarith
    · simpa only [A, if_neg hk, l, r] using (hjoins i).2.2.1
  obtain ⟨a, b, ham, hbm, habDer, hassemble⟩ := exists_saddle_comparison_circle_assembly J2 hJ2
      h hh hhsmall
  obtain ⟨Q, c, Z, hv, hQs, hQt, hqform, hqinv, hq, hqi, hqInj, hqReg,
    hqImage, hqEnds, hcForm, hc, hcCommon, hcQ, hcImages, hZs, hZt, hZform, hZinv,
    hZ, hZi, hJcZ, hZDc, hcZ⟩ := hassemble A gamma hAdata hGammaData hGR hGL hMeet
  let v : E2 := J2.symm (1, 0)
  let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  let Ac : Set UnitCircle := {p | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let Delta : Fin 2 → Set E2 := fun i => c 0 i 0 '' Dc
  have hDelta (i : Fin 2) : Delta i = gamma i '' Icc (0 : ℝ) 1 := (hcImages 0 i 0).1
  have hRange (j i k : Fin 2) : range (c j i k) = Delta i ∪ (A j i k '' Icc l r) := by
    rw [hDelta]
    exact (hcImages j i k).2.1
  have hIntersect (j i k : Fin 2) : Delta i ∩ (A j i k '' Icc l r) = {A j i k l, A j i k r} :=
      by rw [hDelta, ← (hcImages j i k).1]; exact (hcImages j i k).2.2
  have hAIn (j i k : Fin 2) : A j i k '' Icc (0 : ℝ) 1 ⊆ (B j i).closedRegion := by
    by_cases hk : k = 0
    · simpa only [A, if_pos hk] using hAlphaIn j i
    · simpa only [A, if_neg hk] using hbetaIn j i
  have hAProper (j i k : Fin 2) : A j i k '' Ioo (0 : ℝ) 1 ⊆ Kᶜ := by
    by_cases hk : k = 0
    · simpa only [A, if_pos hk] using hProper j i
    · simpa only [A, if_neg hk] using (hproperT i).1
  have hCuts (j i k : Fin 2) : A j i k l ∈ Delta i ∧ A j i k r ∈ Delta i := by
    rw [hDelta]
    exact ⟨⟨1, by constructor <;> norm_num, (hEnds j i k).2⟩, ⟨0, by constructor <;> norm_num,
        (hEnds j i k).1⟩⟩
  have hDeltaK (i : Fin 2) : Delta i ⊆ Kᶜ := by
    rw [hDelta]
    exact (image_mono h01U).trans (hproperT i).2.1
  have hRangeK (j i k : Fin 2) : Disjoint (range (c j i k)) K := by
    apply disjoint_left.mpr
    intro x hx hxK
    rw [hRange j i k] at hx
    rcases hx with hx | hx
    · exact hDeltaK i hx hxK
    · exact hAProper j i k ((image_mono hmid01) hx) hxK
  have hRangeB (j i k : Fin 2) : range (c j i k) ⊆ (B j i).closedRegion := by
    rw [hRange, hDelta]
    have hmidClosed : Icc l r ⊆ Icc (0 : ℝ) 1 :=
      fun _ ht => ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩
    exact union_subset (hgammaIn j i) ((image_mono hmidClosed).trans (hAIn j i k))
  have hRetTail (j i k : Fin 2) : (A j i k '' Icc l r) ∩ (alpha j i '' Tailpar) ⊆ Delta i := by
    rintro x ⟨⟨t, ht, rfl⟩, ⟨s, hs, heq⟩⟩
    have htEnds : t = l ∨ t = r := by
      by_cases hk : k = 0
      · have hst : s = t := by
          apply hAlphaInj j i (h01old (hTail01 hs)) (hUold (hmidU ht))
          simpa only [A, if_pos hk] using heq
        subst s
        rcases hs with hs | hs
        · exact Or.inl (le_antisymm hs.2 ht.1)
        · exact Or.inr (le_antisymm ht.2 hs.1)
      · have hn := (hsectors i).1 ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩
        have ha : alpha j i s = kappa (bn i t) := by simpa only [A, if_neg hk, beta, comp_apply]
            using heq
        have hp := hAnnPar j i s (hTail01 hs) (bn i t) ⟨hn.1, by linarith [hn.2.1]⟩ ha
        have hupper : ‖bn i t‖ ≤ 1 + 3 * h := by
          rcases hs with hs | hs <;> rcases hp with hp | hp <;>
            dsimp [l, r] at * <;> linarith [hs.1, hs.2, hn.2.1]
        have he : ‖bn i t‖ = 1 + 3 * h := le_antisymm hupper ((hproperT i).2.2.1 t ht)
        exact ((hproperT i).2.2.2.1 t ht).mp he
    rcases htEnds with rfl | rfl
    · exact (hCuts j i k).1
    · exact (hCuts j i k).2
  have hTailMeet (j i k : Fin 2) : range (c j i k) ∩ (alpha j i '' Tailpar) ⊆ Delta i := by
    rintro x ⟨hx, ht⟩
    rw [hRange] at hx
    exact hx.elim id (fun hx => hRetTail j i k ⟨hx, ht⟩)
  have hGerm (j i : Fin 2) : EqOn (alpha j i) (beta i) Gpar := by
    intro t ht
    rcases ht with ht | ht
    · have htU : t ∈ U := by dsimp [Gpar, U, l, eta] at *; constructor <;> linarith [ht.1, ht.2]
      rw [hInitial j i t (by rw [abs_lt]; dsimp [l, eta] at ht; constructor <;> linarith [ht.1,
          ht.2]),
        (hgerms i t htU).1 (by dsimp [l, eta] at ht; linarith [ht.2])]
    · have htU : t ∈ U := by dsimp [Gpar, U, r, eta] at *; constructor <;> linarith [ht.1, ht.2]
      rw [hTerminal j i t (by rw [abs_lt]; dsimp [r, eta] at ht; constructor <;> linarith [ht.1,
          ht.2]),
        (hgerms i t htU).2.1 (by dsimp [r, eta] at ht; linarith [ht.1])]
  have hAEnds (j i k : Fin 2) : A j i k 0 ∈ Kboundary ∧ A j i k 1 ∈ Kboundary := by
    constructor
    · rw [hAL j i k 0 (h01U ⟨le_rfl, zero_le_one⟩) (by simpa using hnu) (by linarith)]
      refine ⟨port (ep (i, 0)), ?_, by simp⟩
      exact mem_sphere_zero_iff_norm.mpr (hport _)
    · rw [hAR j i k 1 (h01U ⟨zero_le_one, le_rfl⟩) (by simpa using hnu) (by linarith)]
      refine ⟨port (ep (i, 1)), ?_, by norm_num⟩
      exact mem_sphere_zero_iff_norm.mpr (hport _)
  let O : Fin 2 → Fin 2 → Set E2 := fun j i => (alpha j (other i) '' Icc (0 : ℝ) 1) ∪ (beta
      (other i) '' Icc (0 : ℝ) 1)
  let Protected : Fin 2 → Fin 2 → Set E2 := fun j i => K ∪ (alpha j (other i) '' Icc (0 : ℝ) 1)
      ∪ (beta (other i) '' Icc (0 : ℝ) 1) ∪ (alpha j i '' Tailpar)
  have hKsrc : closedBall (0 : E2) 1 ⊆ kappa.source := by
    intro x hx
    apply hsrc
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    linarith
  have hKcompact : IsCompact K := (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      (kappa.continuousOn.mono hKsrc)
  have hKpre : IsPreconnected K := (convex_closedBall (0 : E2) 1).isPreconnected.image kappa
      (kappa.continuousOn.mono hKsrc)
  have hKzero : kappa (0 : E2) ∈ K := ⟨0, by simp, rfl⟩
  have hOther (j i : Fin 2) : O j i ⊆ (B j i).closedRegionᶜ := by
    have hd : Disjoint (B j i).closedRegion (B j (other i)).closedRegion := by
      fin_cases i
      · simpa [other] using hCase j
      · simpa [other] using (hCase j).symm
    intro x hx hxB
    rcases hx with hx | hx
    · exact disjoint_left.mp hd hxB (hAlphaIn j (other i) hx)
    · exact disjoint_left.mp hd hxB (hbetaIn j (other i) hx)
  have hTailBoundary (j i : Fin 2) : alpha j i '' Tailpar ⊆ (B j i).boundary := by
    intro x hx; rw [hBoundary j i]; exact Or.inl ((image_mono hTail01) hx)
  have hfill (j i k : Fin 2) := exists_saddle_common_cap_exterior_filling hP (B j i)
    (c j i k) (hc j i k) K (O j i) (alpha j i '' Tailpar) (Delta i) hKpre
    ⟨kappa 0, hKzero, (hside j i).2.2⟩ (hRangeB j i k) (hRangeK j i k)
    (hOther j i) (hTailBoundary j i) (hTailMeet j i k)
  choose D hD using hfill
  let W : Fin 2 → Fin 2 → Fin 2 → Set E2 := fun j i k => (D j i k).closedRegionᶜ
  have hDb (j i k : Fin 2) : (D j i k).boundary = range (c j i k) := (hD j i k).1
  have hDProtect (j i k : Fin 2) : (D j i k).closedRegion ∩ Protected j i ⊆ Delta i := by
    simpa only [Protected, O, union_assoc] using (hD j i k).2.2.1
  have hKoutside (j i k : Fin 2) : K ⊆ (D j i k).closedRegionᶜ := by
    intro x hx hxd
    exact hDeltaK i (hDProtect j i k ⟨hxd, Or.inl (Or.inl (Or.inl hx))⟩) hx
  have hProtectedClosed (j i : Fin 2) : IsClosed (Protected j i) ∧ K ⊆ Protected j i ∧ alpha j i
      '' Tailpar ⊆ Protected j i := by
    have ha (j i : Fin 2) : IsCompact (alpha j i '' Icc (0 : ℝ) 1) :=
        isCompact_Icc.image_of_continuousOn ((hAlpha j i).continuousOn.mono h01old)
    have hb (i : Fin 2) : IsCompact (beta i '' Icc (0 : ℝ) 1) :=
        isCompact_Icc.image_of_continuousOn ((hregular i).1.continuousOn.mono h01U)
    have ht : IsCompact (alpha j i '' Tailpar) := (isCompact_Icc.union
        isCompact_Icc).image_of_continuousOn ((hAlpha j i).continuousOn.mono (hTail01.trans h01old))
    exact ⟨(((hKcompact.union (ha j (other i))).union (hb (other i))).union ht).isClosed,
      fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inr hx⟩

  have hLowAvoid (j i k : Fin 2) (x : E2) (hx : 1 ≤ ‖x‖ ∧ ‖x‖ < 1 + h) : kappa x ∉ range (c j i
      k) := by
    intro hc'
    rw [hRange, hDelta] at hc'
    rcases hc' with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
    · have hxt : gn i t = x := kappa.injOn (hgnSrc i t (h01U ht)) (hsrc (by linarith [hx.2])) heq
      have hn : 1 + h ≤ ‖gn i t‖ := ((hsectors i).2 ht).1
      rw [hxt] at hn; linarith
    · by_cases hk : k = 0
      · have ha : alpha j i t = kappa x := by simpa only [A, if_pos hk] using heq
        have hp := hAnnPar j i t ⟨(hmid01 ht).1.le, (hmid01 ht).2.le⟩ x ⟨hx.1, by linarith
            [hx.2]⟩ ha
        rcases hp with hp | hp <;> dsimp [l, r] at ht <;> linarith [ht.1, ht.2]
      · have hxt : bn i t = x := kappa.injOn (hbnSrc i t (hmidU ht)) (hsrc (by linarith [hx.2]))
          (by simpa only [A, if_neg hk, beta, comp_apply] using heq)
        have hn : 1 + 3 * h ≤ ‖bn i t‖ := (hproperT i).2.2.1 t ht
        rw [hxt] at hn; linarith
  let radial : Fin 2 → ℝ → E2 := fun i R => J2.symm (0, sign i * R)
  let path : Fin 2 → ℝ → E2 := fun i t => kappa (radial i (1 + h - t))
  have hradialN (i : Fin 2) (R : ℝ) (hR : 0 ≤ R) : ‖radial i R‖ = R := by
    have hs : (sign i) ^ 2 = 1 := by fin_cases i <;> norm_num [sign]
    have hn := hnorm 0 (sign i * R)
    change ‖radial i R‖ ^ 2 = _ at hn
    rw [zero_pow (by norm_num : 2 ≠ 0), zero_add, mul_pow, hs, one_mul] at hn
    exact (sq_eq_sq₀ (norm_nonneg _) hR).mp hn
  have hradialC (i : Fin 2) : Continuous (radial i) := by dsimp [radial]; fun_prop
  have hpathC (i : Fin 2) : ContinuousAt (path i) 0 := by
    have hx : radial i (1 + h) ∈ kappa.source := hsrc (by rw [hradialN i _ (by linarith)]; linarith)
    have hk := kappa.continuousOn.continuousAt (kappa.open_source.mem_nhds hx)
    have hi : ContinuousAt (fun t : ℝ => radial i (1 + h - t)) 0 := (hradialC
        i).continuousAt.comp (continuous_const.sub continuous_id).continuousAt
    exact hk.comp_of_eq hi (by simp only [sub_zero])
  have hpath0 (i : Fin 2) : path i 0 = gamma i (1 / 2) := by simpa only [path, radial, sub_zero]
      using (hjoins i).2.2.2.symm
  have hpathOutside (i : Fin 2) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) h) (j k : Fin 2) : path i t ∈ (D j
      i k).closedRegionᶜ := by
    let R : ℝ := 1 + h - t
    let S : Set E2 := kappa '' (radial i '' Icc 1 R)
    have hRS (s : ℝ) (hs : s ∈ Icc 1 R) : radial i s ∈ kappa.source := by
      apply hsrc
      rw [hradialN i s (by linarith [hs.1])]
      dsimp [R] at hs
      linarith [hs.2, ht.1]
    have hS : IsPreconnected S := by
      apply (isPreconnected_Icc.image (radial i) (hradialC i).continuousOn).image
      apply kappa.continuousOn.mono
      rintro x ⟨s, hs, rfl⟩
      exact hRS s hs
    have hSbd : Disjoint S (D j i k).boundary := by
      apply disjoint_left.mpr
      rintro x ⟨_, ⟨s, hs, rfl⟩, rfl⟩ hxb
      rw [hDb] at hxb
      exact hLowAvoid j i k (radial i s) ⟨by rw [hradialN i s (by linarith [hs.1])]; exact hs.1,
        by rw [hradialN i s (by linarith [hs.1])]; dsimp [R] at hs; linarith [hs.2, ht.1]⟩ hxb
    have hpK : kappa (radial i 1) ∈ K := ⟨radial i 1, by simp only [mem_closedBall,
        dist_zero_right, hradialN i 1 zero_le_one, le_refl], rfl⟩
    have hpS : kappa (radial i 1) ∈ S := ⟨radial i 1, ⟨1, ⟨le_rfl, by dsimp [R]; linarith
        [ht.2]⟩, rfl⟩, rfl⟩
    rcases (D j i k).preconnected_subset_inside_or_outside hS hSbd with hi | ho
    · apply False.elim
      apply hKoutside j i k hpK
      rw [← (D j i k).inside_union_boundary]
      exact Or.inl (hi hpS)
    · exact ho ⟨radial i R, ⟨R, ⟨by dsimp [R]; linarith [ht.2], le_rfl⟩, rfl⟩, rfl⟩

  have hInner : Continuous (fun p : UnitCircle => ⟪v, (p : E2)⟫_ℝ) := continuous_const.inner
      continuous_subtype_val
  have hAcCompact : IsCompact Ac := (isClosed_le continuous_const hInner).isCompact
  have hJcOpen : IsOpen Jc := isOpen_lt continuous_const hInner
  have hDcAc : Dc ⊆ Ac := by
    intro p hp
    change (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ
    change (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ at hp
    linarith
  have hAcJc : Ac ⊆ Jc := by
    intro p hp
    change (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ
    change (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ at hp
    linarith
  have hAcZ : Ac ⊆ Z.source := hAcJc.trans hJcZ
  have hzero : (0 : ℝ) ∈ Z '' Dc := by rw [hZDc]; constructor <;> norm_num
  have hone : (1 : ℝ) ∈ Z '' Dc := by rw [hZDc]; constructor <;> norm_num
  obtain ⟨p0, hp0, hz0⟩ := hzero
  obtain ⟨p1, hp1, hz1⟩ := hone
  obtain ⟨pmin, hpmin, hmin⟩ := hAcCompact.exists_isMinOn ⟨p0, hDcAc hp0⟩ (Z.continuousOn.mono hAcZ)
  obtain ⟨pmax, hpmax, hmax⟩ := hAcCompact.exists_isMaxOn ⟨p0, hDcAc hp0⟩ (Z.continuousOn.mono hAcZ)
  have hminTarget : Z pmin ∈ Ioo (-eta) (1 + eta) := by rw [← hZt]; exact Z.map_source (hAcZ hpmin)
  have hmaxTarget : Z pmax ∈ Ioo (-eta) (1 + eta) := by rw [← hZt]; exact Z.map_source (hAcZ hpmax)
  let L : ℝ := (-eta + Z pmin) / 2
  let R : ℝ := (Z pmax + (1 + eta)) / 2
  have hL : -eta < L ∧ L < Z pmin := by dsimp [L]; constructor <;> linarith [hminTarget.1]
  have hR : Z pmax < R ∧ R < 1 + eta := by dsimp [R]; constructor <;> linarith [hmaxTarget.2]
  have hL0 : L < 0 := by
    have hm : Z pmin ≤ Z p0 := hmin (hDcAc hp0)
    rw [hz0] at hm
    linarith [hL.2]
  have h1R : 1 < R := by
    have hm : Z p1 ≤ Z pmax := hmax (hDcAc hp1)
    rw [hz1] at hm
    linarith [hR.1]
  have hLR : L < R := by linarith
  let Uc : Set UnitCircle := (Z.source ∩ Z ⁻¹' Ioo L R) ∩ Jc
  have hUc : IsOpen Uc := (Z.isOpen_inter_preimage isOpen_Ioo).inter hJcOpen
  have hAcUc : Ac ⊆ Uc := fun p hp => ⟨⟨hAcZ hp, ⟨hL.2.trans_le (hmin hp), (hmax hp).trans_lt
      hR.1⟩⟩, hAcJc hp⟩
  have hUcJc : Uc ⊆ Jc := inter_subset_right
  have hNsource (i : Fin 2) : Ioo (-eta) (1 + eta) ×ˢ ({0} : Set ℝ) ⊆ (N0 i).source := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    apply (hN0 i).1
    exact ⟨⟨by dsimp [eta] at ht; linarith [ht.1], by dsimp [eta] at ht; linarith [ht.2]⟩, ⟨by
        linarith, hw0.le⟩⟩
  have hNzero (i : Fin 2) (t : ℝ) (ht : t ∈ Ioo (-eta) (1 + eta)) : N0 i (t, 0) = gamma i t := by
    rw [(hN0 i).2.2.2.2.2 (t, 0) (hNsource i ⟨ht, rfl⟩), zero_smul, add_zero]
  have hhalf (i : Fin 2) : ∃ (w s : ℝ), 0 < w ∧ (s = 1 ∨ s = -1) ∧
      Icc L R ×ˢ Icc (-w) w ⊆ (N0 i).source ∧
      ∀ a : Fin 4, N0 i '' (Ioo L R ×ˢ {z : ℝ | 0 < s * z ∧ |z| < w}) ⊆
        (D (ep.symm a).1 i (ep.symm a).2).closedRegionᶜ := by
    exact exists_saddle_common_exterior_half_strip
      (fun a : Fin 4 => D (ep.symm a).1 i (ep.symm a).2)
      (fun a : Fin 4 => c (ep.symm a).1 i (ep.symm a).2)
      (fun a => hc (ep.symm a).1 i (ep.symm a).2)
      (fun a => hDb (ep.symm a).1 i (ep.symm a).2)
      Z (gamma i) (-eta) (1 + eta) L R hL.1 hLR hR.2 hZt
      (fun a p hp => hcZ (ep.symm a).1 i (ep.symm a).2 p hp)
      (N0 i) (hNsource i) (hNzero i) (1 / 2) ⟨by linarith, by linarith⟩
      (path i) (hpathC i) (hpath0 i) h hh
      (fun t ht a => hpathOutside i t ht (ep.symm a).1 (ep.symm a).2)
  choose widths signs hwidth hsign hrect hpositive using hhalf
  let w : ℝ := min (widths 0) (widths 1)
  have hw : 0 < w := lt_min (hwidth 0) (hwidth 1)
  have hwle (i : Fin 2) : w ≤ widths i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hsignSq (i : Fin 2) : signs i * signs i = 1 := by rcases hsign i with hs | hs <;> rw [hs]
      <;> norm_num
  have hsignAbs (i : Fin 2) : |signs i| = 1 := by rcases hsign i with hs | hs <;> rw [hs] <;>
      norm_num
  let Ref : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := fun i => {
    toFun := fun p => (p.1, signs i * p.2)
    invFun := fun p => (p.1, signs i * p.2)
    source := univ, target := univ
    map_source' := fun _ _ => mem_univ _, map_target' := fun _ _ => mem_univ _
    left_inv' := fun p _ => by
      apply Prod.ext
      · rfl
      · change signs i * (signs i * p.2) = p.2
        rw [← mul_assoc, hsignSq, one_mul]
    right_inv' := fun p _ => by
      apply Prod.ext
      · rfl
      · change signs i * (signs i * p.2) = p.2
        rw [← mul_assoc, hsignSq, one_mul]
    open_source := isOpen_univ, open_target := isOpen_univ
    continuousOn_toFun := (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
    continuousOn_invFun := (continuous_fst.prodMk (continuous_const.mul
        continuous_snd)).continuousOn }
  have hRef (i : Fin 2) : ContDiff ℝ ∞ (Ref i) := contDiff_fst.prodMk (contDiff_const.mul
      contDiff_snd)
  have hRefInv (i : Fin 2) : ContDiff ℝ ∞ (Ref i).symm := contDiff_fst.prodMk
      (contDiff_const.mul contDiff_snd)
  let P := Z.prod (OpenPartialHomeomorph.refl ℝ)
  have hPs : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ P P.source := by
    have hp : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ P P.source :=
      hZ.prodMap contMDiff_id.contMDiffOn
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hp
    exact hp
  have hPi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ P.symm P.target := by
    have hp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ P.symm P.target :=
      hZi.prodMap contMDiff_id.contMDiffOn
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hp
    exact hp
  let N : Fin 2 → OpenPartialHomeomorph (UnitCircle × ℝ) E2 := fun i => (P.trans (Ref i)).trans
      (N0 i)
  have hNform (i : Fin 2) (p : UnitCircle) (s : ℝ) : N i (p, s) = N0 i (Z p, signs i * s) := rfl
  have hNs (i : Fin 2) : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ (N i) (N i).source := by
    have hp : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (P.trans (Ref i)) (P.trans (Ref
        i)).source :=
      (hRef i).contMDiff.contMDiffOn.comp (hPs.mono inter_subset_left) (fun _ hp => hp.2)
    exact (hN0 i).2.2.2.1.contMDiffOn.comp (hp.mono inter_subset_left) (fun _ hp => hp.2)
  have hNi (i : Fin 2) : ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (N i).symm (N i).target
      := by
    have hp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (P.trans (Ref i)).symm (P.trans
        (Ref i)).target :=
      hPi.comp ((hRefInv i).contMDiff.contMDiffOn.mono inter_subset_left) (fun _ hp => hp.2)
    exact hp.comp ((hN0 i).2.2.2.2.1.contMDiffOn.mono inter_subset_left) (fun _ hp => hp.2)
  have hNbuffer (i : Fin 2) : Uc ×ˢ Icc (-w) w ⊆ (N i).source := by
    rintro ⟨p, s⟩ ⟨hp, hs⟩
    refine ⟨⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩, ?_⟩
    change (Z p, signs i * s) ∈ (N0 i).source
    apply hrect i
    have habs : |signs i * s| ≤ widths i := by
      rw [abs_mul, hsignAbs, one_mul]
      exact (abs_le.mpr hs).trans (hwle i)
    exact ⟨⟨hp.1.2.1.le, hp.1.2.2.le⟩, abs_le.mp habs⟩
  have hNcentral (i : Fin 2) (p : UnitCircle) (hp : p ∈ Uc) : N i (p, 0) = c 0 i 0 p := by
    rw [hNform, mul_zero, hNzero i (Z p) (by rw [← hZt]; exact Z.map_source hp.1.1)]
    exact (hcZ 0 i 0 p hp.1.1).symm
  have hNpositive (i j k : Fin 2) : N i '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ W j i k := by
    rintro x ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
    rw [hNform]
    have hmul : 0 < signs i * (signs i * s) := by rw [← mul_assoc, hsignSq, one_mul]; exact hs.1
    have habs : |signs i * s| < widths i := by
      rw [abs_mul, hsignAbs, one_mul, abs_of_pos hs.1]
      exact hs.2.trans_le (hwle i)
    have hi := hpositive i (ep (j, k)) ⟨(Z p, signs i * s), ⟨hp.1.2, hmul, habs⟩, rfl⟩
    simpa only [W, Equiv.symm_apply_apply] using hi
  have hAfinal (j i k : Fin 2) : ContDiffOn ℝ ∞ (A j i k) Uarc ∧ InjOn (A j i k) Uarc ∧
      (∀ t ∈ Uarc, deriv (A j i k) t ≠ 0) ∧ A j i k 0 ∈ Kboundary ∧ A j i k 1 ∈ Kboundary ∧ A j
          i k '' Ioo (0 : ℝ) 1 ⊆ Kᶜ :=
    ⟨(hAdata j i k).1.mono hArcU, (hAdata j i k).2.1.mono hArcU,
      fun t ht => (hAdata j i k).2.2 t (hArcU ht), (hAEnds j i k).1, (hAEnds j i k).2, hAProper
          j i k⟩
  have hRangeFinal (j i k : Fin 2) : range (c j i k) = Delta i ∪ (A j i k '' Icc l r) ∧
      Delta i ∩ (A j i k '' Icc l r) = {A j i k l, A j i k r} ∧ Disjoint (range (c j i k)) K ∧
          range (c j i k) ∩ Protected j i ⊆ Delta i := by
    refine ⟨hRange j i k, hIntersect j i k, hRangeK j i k, ?_⟩
    rintro x ⟨hx, hp⟩
    apply hDProtect j i k ⟨?_, hp⟩
    rw [← (D j i k).inside_union_boundary, hDb]
    exact Or.inr hx
  have hWfinal (j i k : Fin 2) : IsOpen (W j i k) ∧ IsConnected (W j i k) ∧
      ¬ Bornology.IsBounded (W j i k) ∧ Disjoint (W j i k) (range (c j i k)) ∧ Protected j i \
          Delta i ⊆ W j i k := by
    simpa only [W, Protected, O, union_assoc] using (hD j i k).2.2.2
  have hnums : 0 < eta ∧ eta < h / 8 ∧ 0 < l ∧ l < r ∧ r < 1 ∧ eta < l ∧ r + eta < 1 ∧ l + eta <
      r - eta := by
    dsimp [eta, l, r]
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  exact ⟨h, l, r, eta, beta, c, Q, W, Uc, w, N, hh, hhnu, hhsmall, rfl, rfl,
    hnums.1, hnums.2.1, hnums.2.2.1, hnums.2.2.2.1, hnums.2.2.2.2.1,
    hnums.2.2.2.2.2.1, hnums.2.2.2.2.2.2.1, hnums.2.2.2.2.2.2.2,
    hv, hProtectedClosed, hAfinal, fun j i => ⟨hGerm j i, hbetaIn j i⟩,
    hbetaPair, hc, hcCommon, hq, hqInj, hqReg, hqImage, hqEnds, hcQ, hRangeFinal,
    hWfinal, hUc, hAcUc, hUcJc, hw,
    fun i => ⟨hNbuffer i, hNs i, hNi i, hNcentral i, fun j k => hNpositive i j k⟩⟩

end PoincareConjecture.M25.Topology3D
