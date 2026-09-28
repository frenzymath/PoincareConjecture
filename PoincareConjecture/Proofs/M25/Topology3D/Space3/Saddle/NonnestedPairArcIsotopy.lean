import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedCommonCapInputs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RelativeExteriorArc
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

set_option linter.unusedVariables false in

theorem exists_nonnested_pair_arc_isotopy
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
      ∃ (l r eta : ℝ) (C : Set E2)
        (J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞),
      let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
      0 < l ∧ l < r ∧ r < 1 ∧ l < nu ∧ 1 - nu < r ∧
      0 < eta ∧ eta < l ∧ r + eta < 1 ∧ l + eta < r - eta ∧
      IsCompact C ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) ∧
      (∀ s : ℝ, s ≤ 0 → ∀ y : E2, J s y = y ∧ (J s).symm y = y) ∧
      (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
        J s y = J 1 y ∧ (J s).symm y = (J 1).symm y) ∧
      (∀ s : ℝ,
        tsupport (fun y : E2 => J s y - y) ⊆ C ∧
        tsupport (fun y : E2 => (J s).symm y - y) ⊆ C) ∧
      (∀ s : ℝ, ∀ y : E2, y ∉ C → J s y = y ∧ (J s).symm y = y) ∧
      IsOpen Cᶜ ∧ K ⊆ Cᶜ ∧
      (∀ j i : Fin 2, alpha j i '' Tailpar ⊆ Cᶜ) ∧
      (∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
        J 1 (alpha 0 i t) = alpha 1 i t ∧
        (J 1).symm (alpha 1 i t) = alpha 0 i t) ∧
      ∀ i : Fin 2,
        (J 1) '' (alpha 0 i '' Icc (0 : ℝ) 1) = alpha 1 i '' Icc (0 : ℝ) 1 ∧
        (J 1).symm '' (alpha 1 i '' Icc (0 : ℝ) 1) = alpha 0 i '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  intro nu hnu hnuSmall alpha hAlpha hAlphaInj hAlphaReg hPair hProper
    hInitial hTerminal B hBoundary hCase
  obtain ⟨h, l, r, eta, beta, c, q, W, Uc, w, N,
    hh, hhnu, hhsmall, hlform, hrform, heta, hetah, hl, hlr, hr, hetal, hetar,
    hgap, hv, hProtected, hA, hGerm, hBetaPair, hc, hcCommon, hq, hqInj, hqReg,
    hqImage, hqEnds, hTracks, hCurve, hW, hUc, hAc, hUcJ, hw, hN⟩ :=
    exists_nonnested_common_cap_inputs hP kappa hkappaSource hkappa hkappaInv
      J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne
      nu hnu hnuSmall alpha hAlpha hAlphaInj hAlphaReg hPair hProper
      hInitial hTerminal B hBoundary hCase
  let K : Set E2 := kappa '' closedBall (0 : E2) 1
  let Kboundary : Set E2 := kappa '' sphere (0 : E2) 1
  let v : E2 := J2.symm (1, 0)
  let Uarc : Set ℝ := Ioo (-eta) (1 + eta)
  let Gpar : Set ℝ := Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)
  let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
  let Umid : Set ℝ := Ioo (l - eta) (r + eta)
  let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  let Delta : Fin 2 → Set E2 := fun i => c 0 i 0 '' Dc
  let A : Fin 2 → Fin 2 → Fin 2 → ℝ → E2 :=
    fun j i k => if k = 0 then alpha j i else beta i
  let other : Fin 2 → Fin 2 := Equiv.swap (0 : Fin 2) 1
  let Protected : Fin 2 → Fin 2 → Set E2 := fun j i =>
    K ∪ (alpha j (other i) '' Icc (0 : ℝ) 1) ∪
      (beta (other i) '' Icc (0 : ℝ) 1) ∪ (alpha j i '' Tailpar)
  change ∀ j i, IsClosed (Protected j i) ∧ K ⊆ Protected j i ∧
    alpha j i '' Tailpar ⊆ Protected j i at hProtected
  change ∀ j i k, ContDiffOn ℝ ∞ (A j i k) Uarc ∧ InjOn (A j i k) Uarc ∧
    (∀ t ∈ Uarc, deriv (A j i k) t ≠ 0) ∧
    A j i k 0 ∈ Kboundary ∧ A j i k 1 ∈ Kboundary ∧
    A j i k '' Ioo (0 : ℝ) 1 ⊆ Kᶜ at hA
  change ∀ j i, EqOn (alpha j i) (beta i) Gpar ∧
    beta i '' Icc (0 : ℝ) 1 ⊆ (B j i).closedRegion at hGerm
  change ∀ j i k, EqOn (c j i k) (c 0 i 0) Jc at hcCommon
  change ∀ j i k,
    range (c j i k) = Delta i ∪ (A j i k '' Icc l r) ∧
    Delta i ∩ (A j i k '' Icc l r) = {A j i k l, A j i k r} ∧
    Disjoint (range (c j i k)) K ∧
    range (c j i k) ∩ Protected j i ⊆ Delta i at hCurve
  change ∀ j i k, IsOpen (W j i k) ∧ IsConnected (W j i k) ∧
    ¬ Bornology.IsBounded (W j i k) ∧ Disjoint (W j i k) (range (c j i k)) ∧
    Protected j i \ Delta i ⊆ W j i k at hW
  change Uc ⊆ Jc at hUcJ
  have hsource1 : closedBall (0 : E2) 1 ⊆ kappa.source := by
    intro x hx
    apply hkappaSource
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    linarith
  have hDcJ : Dc ⊆ Jc := by
    intro p hp
    change (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ at hp
    change (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ
    linarith
  have hDeltaEq (j i : Fin 2) : c j i 0 '' Dc = Delta i := by
    change c j i 0 '' Dc = c 0 i 0 '' Dc
    exact image_congr (fun p hp => hcCommon j i 0 (hDcJ hp))
  have hCircleCommon (j i : Fin 2) : EqOn (c j i 0) (c j i 1) Jc :=
    fun p hp => (hcCommon j i 0 hp).trans (hcCommon j i 1 hp).symm
  have hNzero (j i : Fin 2) (p : UnitCircle) (hp : p ∈ Uc) :
      N i (p, 0) = c j i 0 p :=
    ((hN i).2.2.2.1 p hp).trans (hcCommon j i 0 (hUcJ hp)).symm
  have hGerms (j i : Fin 2) : EqOn (A j i 0) (A j i 1) Gpar := by
    simpa only [A, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
      using (hGerm j i).1
  have hAtails (j i : Fin 2) : A j i 0 '' Tailpar ⊆ Protected j i := by
    simpa only [A, if_pos rfl] using (hProtected j i).2.2
  have hcall (j i : Fin 2) :
      ∃ (C0 : Set E2)
        (H : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞),
        IsCompact C0 ∧ C0 ⊆ (Protected j i)ᶜ ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => H p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => (H p.1).symm p.2) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ y : E2, H s y = y ∧ (H s).symm y = y) ∧
        (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
          H s y = H 1 y ∧ (H s).symm y = (H 1).symm y) ∧
        (∀ s : ℝ, ∀ y : E2, y ∉ C0 → H s y = y ∧ (H s).symm y = y) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          H 1 (alpha j i t) = beta i t ∧ (H 1).symm (beta i t) = alpha j i t := by
    obtain ⟨C0, H, rho, hC0, hfree, hH, hHi, hzero, hone, _, hfix,
      _, _, _, _, _, hpoint, _, _⟩ :=
      exists_relative_exterior_arc_isotopy hP kappa hsource1 hkappa hkappaInv
        (A j i) l r eta (Protected j i) v (c j i) q (W j i) Uc w (N i)
        hl hlr hr heta hetal hetar hgap (hProtected j i).1 (hProtected j i).2.1
        (fun k => (hA j i k).1) (fun k => (hA j i k).2.1)
        (fun k => (hA j i k).2.2.1)
        (fun k => ⟨(hA j i k).2.2.2.1, (hA j i k).2.2.2.2.1⟩)
        (fun k => (hA j i k).2.2.2.2.2) (hGerms j i) (hAtails j i)
        hv (hc j i) (hCircleCommon j i) hq hqInj hqReg hqImage hqEnds
        (hTracks j i) (fun k => (hCurve j i k).2.2.1)
        (fun k => by
          change range (c j i k) ∩ Protected j i ⊆ c j i 0 '' Dc
          rw [hDeltaEq j i]
          exact (hCurve j i k).2.2.2)
        (fun k => (hW j i k).1) (fun k => (hW j i k).2.1)
        (fun k => (hW j i k).2.2.1) (fun k => (hW j i k).2.2.2.1)
        (fun k => by
          change Protected j i \ (c j i 0 '' Dc) ⊆ W j i k
          rw [hDeltaEq j i]
          exact (hW j i k).2.2.2.2)
        hUc hAc hUcJ hw (hN i).1 (hN i).2.1 (hN i).2.2.1
        (hNzero j i) ((hN i).2.2.2.2 j)
    refine ⟨C0, H, hC0, fun y hy => (hfree hy).1, hH, hHi, hzero, hone, hfix, ?_⟩
    simpa only [A, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hpoint
  choose C0 H hC0 hfree hH hHi hzero hone hfix hpoint using hcall
  have hProtectedFix (j i : Fin 2) (s : ℝ) (y : E2) (hy : y ∈ Protected j i) :
      H j i s y = y ∧ (H j i s).symm y = y :=
    hfix j i s y (fun hyC => hfree j i hyC hy)
  have hTailG : Tailpar ⊆ Gpar := by
    rintro t (ht | ht)
    · exact Or.inl ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hTail01 : Tailpar ⊆ Icc (0 : ℝ) 1 := by
    rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hTailEq (j i : Fin 2) (t : ℝ) (ht : t ∈ Tailpar) : alpha j i t = beta i t :=
    (hGerm j i).1 (hTailG ht)
  have hTailProtected (j i j' i' : Fin 2) (t : ℝ) (ht : t ∈ Tailpar) :
      alpha j' i' t ∈ Protected j i := by
    by_cases hi : i' = i
    · subst i'
      rw [hTailEq j' i t ht, ← hTailEq j i t ht]
      exact (hProtected j i).2.2 ⟨t, ht, rfl⟩
    · have hi' : i' = other i := by
        fin_cases i <;> fin_cases i' <;> simp_all [other]
      rw [hi', hTailEq j' (other i) t ht]
      exact Or.inl (Or.inr ⟨t, hTail01 ht, rfl⟩)
  let C : Set E2 := (C0 0 0 ∪ C0 0 1) ∪ (C0 1 0 ∪ C0 1 1)
  have hC : IsCompact C := ((hC0 0 0).union (hC0 0 1)).union
    ((hC0 1 0).union (hC0 1 1))
  have hCin (j i : Fin 2) : C0 j i ⊆ C := by
    intro y hy
    fin_cases j <;> fin_cases i
    · exact Or.inl (Or.inl hy)
    · exact Or.inl (Or.inr hy)
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
  have hNoC (y : E2) (hy : ∀ j i : Fin 2, y ∉ C0 j i) : y ∉ C := by
    rintro ((hy00 | hy01) | (hy10 | hy11))
    · exact hy 0 0 hy00
    · exact hy 0 1 hy01
    · exact hy 1 0 hy10
    · exact hy 1 1 hy11
  have hKC : K ⊆ Cᶜ := by
    intro y hy
    apply hNoC
    intro j i hyC
    exact hfree j i hyC ((hProtected j i).2.1 hy)
  have hTailsC (j' i' : Fin 2) : alpha j' i' '' Tailpar ⊆ Cᶜ := by
    rintro y ⟨t, ht, rfl⟩
    apply hNoC
    intro j i hyC
    exact hfree j i hyC (hTailProtected j i j' i' t ht)
  have hOtherAlpha (j i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      alpha j (other i) t ∈ Protected j i :=
    Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩))
  have hOtherBeta (j i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      beta (other i) t ∈ Protected j i :=
    Or.inl (Or.inr ⟨t, ht, rfl⟩)
  let P : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun j s => (H j 0 s).trans (H j 1 s)
  have hPs (j : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × E2 => P j p.1 p.2) :=
    (hH j 1).comp (contDiff_fst.prodMk (hH j 0))
  have hPi (j : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × E2 => (P j p.1).symm p.2) :=
    (hHi j 0).comp (contDiff_fst.prodMk (hHi j 1))
  have hPfix (j : Fin 2) (s : ℝ) (y : E2) (hy : y ∉ C) :
      P j s y = y ∧ (P j s).symm y = y := by
    have h0 := hfix j 0 s y (fun hy0 => hy (hCin j 0 hy0))
    have h1 := hfix j 1 s y (fun hy1 => hy (hCin j 1 hy1))
    constructor
    · change H j 1 s (H j 0 s y) = y
      rw [h0.1, h1.1]
    · change (H j 0 s).symm ((H j 1 s).symm y) = y
      rw [h1.2, h0.2]
  have hPzero (j : Fin 2) (s : ℝ) (hs : s ≤ 0) (y : E2) :
      P j s y = y ∧ (P j s).symm y = y := by
    constructor
    · change H j 1 s (H j 0 s y) = y
      rw [(hzero j 0 s hs y).1, (hzero j 1 s hs y).1]
    · change (H j 0 s).symm ((H j 1 s).symm y) = y
      rw [(hzero j 1 s hs y).2, (hzero j 0 s hs y).2]
  have hPone (j : Fin 2) (s : ℝ) (hs : 1 ≤ s) (y : E2) :
      P j s y = P j 1 y ∧ (P j s).symm y = (P j 1).symm y := by
    constructor
    · change H j 1 s (H j 0 s y) = H j 1 1 (H j 0 1 y)
      rw [(hone j 0 s hs y).1, (hone j 1 s hs (H j 0 1 y)).1]
    · change (H j 0 s).symm ((H j 1 s).symm y) =
        (H j 0 1).symm ((H j 1 1).symm y)
      rw [(hone j 1 s hs y).2, (hone j 0 s hs ((H j 1 1).symm y)).2]
  have hPend (j i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      P j 1 (alpha j i t) = beta i t := by
    fin_cases i
    · change H j 1 1 (H j 0 1 (alpha j 0 t)) = beta 0 t
      rw [(hpoint j 0 t ht).1]
      exact (hProtectedFix j 1 1 (beta 0 t)
        (by simpa [other] using hOtherBeta j 1 t ht)).1
    · change H j 1 1 (H j 0 1 (alpha j 1 t)) = beta 1 t
      rw [(hProtectedFix j 0 1 (alpha j 1 t)
        (by simpa [other] using hOtherAlpha j 0 t ht)).1]
      exact (hpoint j 1 t ht).1
  have hPendInv (j i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (P j 1).symm (beta i t) = alpha j i t := by
    rw [← hPend j i t ht, (P j 1).symm_apply_apply]
  let J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun s => (P 0 s).trans (P 1 s).symm
  have hJs : ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) :=
    (hPi 1).comp (contDiff_fst.prodMk (hPs 0))
  have hJi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) :=
    (hPi 0).comp (contDiff_fst.prodMk (hPs 1))
  have hJfix (s : ℝ) (y : E2) (hy : y ∉ C) :
      J s y = y ∧ (J s).symm y = y := by
    constructor
    · change (P 1 s).symm (P 0 s y) = y
      rw [(hPfix 0 s y hy).1, (hPfix 1 s y hy).2]
    · change (P 0 s).symm (P 1 s y) = y
      rw [(hPfix 1 s y hy).1, (hPfix 0 s y hy).2]
  have hJzero (s : ℝ) (hs : s ≤ 0) (y : E2) :
      J s y = y ∧ (J s).symm y = y := by
    constructor
    · change (P 1 s).symm (P 0 s y) = y
      rw [(hPzero 0 s hs y).1, (hPzero 1 s hs y).2]
    · change (P 0 s).symm (P 1 s y) = y
      rw [(hPzero 1 s hs y).1, (hPzero 0 s hs y).2]
  have hJone (s : ℝ) (hs : 1 ≤ s) (y : E2) :
      J s y = J 1 y ∧ (J s).symm y = (J 1).symm y := by
    constructor
    · change (P 1 s).symm (P 0 s y) = (P 1 1).symm (P 0 1 y)
      rw [(hPone 0 s hs y).1, (hPone 1 s hs (P 0 1 y)).2]
    · change (P 0 s).symm (P 1 s y) = (P 0 1).symm (P 1 1 y)
      rw [(hPone 1 s hs y).1, (hPone 0 s hs (P 1 1 y)).2]
  have hSupport (s : ℝ) : tsupport (fun y : E2 => J s y - y) ⊆ C ∧
      tsupport (fun y : E2 => (J s).symm y - y) ⊆ C := by
    constructor
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hyC
      exact hy (sub_eq_zero.mpr (hJfix s y hyC).1)
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hyC
      exact hy (sub_eq_zero.mpr (hJfix s y hyC).2)
  have hJend (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      J 1 (alpha 0 i t) = alpha 1 i t := by
    change (P 1 1).symm (P 0 1 (alpha 0 i t)) = alpha 1 i t
    rw [hPend 0 i t ht, hPendInv 1 i t ht]
  have hJendInv (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (J 1).symm (alpha 1 i t) = alpha 0 i t := by
    rw [← hJend i t ht, (J 1).symm_apply_apply]
  have hlnu : l < nu := by rw [hlform]; linarith
  have hrnu : 1 - nu < r := by rw [hrform]; linarith
  refine ⟨l, r, eta, C, J, hl, hlr, hr, hlnu, hrnu, heta, hetal, hetar,
    hgap, hC, hJs, hJi, hJzero, hJone, hSupport, hJfix,
    hC.isClosed.isOpen_compl, hKC, hTailsC,
    (fun i t ht => ⟨hJend i t ht, hJendInv i t ht⟩), ?_⟩
  intro i
  constructor
  · rw [← image_comp]
    exact image_congr (fun t ht => hJend i t ht)
  · rw [← image_comp]
    exact image_congr (fun t ht => hJendInv i t ht)

end PoincareConjecture.M25.Topology3D
