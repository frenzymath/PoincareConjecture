import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SmoothTransitionRegular
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarCurveNormalChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in



theorem exists_saddle_short_sector_templates
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) :
    let sigma : ℝ → ℝ := Real.smoothTransition
    let sign : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let other : Fin 2 → Fin 2 := Equiv.swap (0 : Fin 2) 1
    let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
    let K := kappa '' closedBall (0 : E2) 1
    let rb : ℝ → ℝ := fun t => 1 + 5 * h +
      (t - 5 * h) * (1 - sigma ((t - 4 * h) / (2 * h))) +
      (1 - t - 5 * h) * (1 - sigma ((1 - t - 4 * h) / (2 * h)))
    let ab : ℝ → ℝ := fun t => Real.pi / 4 +
      (Real.pi / 2) * sigma ((t - 4 * h) / (1 - 8 * h))
    let rg : ℝ → ℝ := fun t => 1 + h +
      (2 * h - t) * (1 - sigma ((t - h) / h)) +
      (2 * h - (1 - t)) * (1 - sigma ((1 - t - h) / h))
    let ag : ℝ → ℝ := fun t => 3 * Real.pi / 4 -
      (Real.pi / 2) * sigma ((t - h) / (1 - 2 * h))
    let b : Fin 2 → ℝ → E2 := fun i t => J2.symm
      (sign i * rb t * Real.cos (ab t), sign i * rb t * Real.sin (ab t))
    let g : Fin 2 → ℝ → E2 := fun i t => J2.symm
      (sign i * rg t * Real.cos (ag t), sign i * rg t * Real.sin (ag t))
    let beta : Fin 2 → ℝ → E2 := fun i => kappa ∘ b i
    let gamma : Fin 2 → ℝ → E2 := fun i => kappa ∘ g i
    let rot : E2 → E2 := fun v => J2.symm (-(J2 v).2, (J2 v).1)
    ∃ (w : ℝ) (N : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) E2),
      0 < w ∧
      (∀ i, ContDiff ℝ ∞ (b i) ∧ ContDiff ℝ ∞ (g i)) ∧
      (∀ i t, t ∈ U →
        ‖b i t‖ = rb t ∧ 0 < rb t ∧ rb t < 2 ∧
        ‖g i t‖ = rg t ∧ 1 < rg t ∧ rg t < 2) ∧
      (∀ i,
        ContDiffOn ℝ ∞ (beta i) U ∧ Set.InjOn (beta i) U ∧
        (∀ t ∈ U, deriv (beta i) t ≠ 0) ∧
        ContDiffOn ℝ ∞ (gamma i) U ∧ Set.InjOn (gamma i) U ∧
        (∀ t ∈ U, deriv (gamma i) t ≠ 0)) ∧
      (∀ i t, t ∈ U →
        (t ≤ 4 * h → beta i t = kappa ((1 + t) • port (ep (i, 0)))) ∧
        (1 - 4 * h ≤ t → beta i t = kappa ((2 - t) • port (ep (i, 1)))) ∧
        (t ≤ h → gamma i t = kappa ((1 + 3 * h - t) • port (ep (i, 1)))) ∧
        (1 - h ≤ t → gamma i t = kappa ((1 + 3 * h + t - 1) • port (ep (i, 0))))) ∧
      (∀ i,
        Set.MapsTo (b i) (Icc (0 : ℝ) 1)
          {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 6 * h ∧ |(J2 x).1| ≤ sign i * (J2 x).2} ∧
        Set.MapsTo (g i) (Icc (0 : ℝ) 1)
          {x | 1 + h ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 3 * h ∧ |(J2 x).1| ≤ sign i * (J2 x).2}) ∧
      (∀ i,
        beta i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ ∧ gamma i '' U ⊆ Kᶜ ∧
        (∀ t ∈ Icc (3 * h) (1 - 3 * h), 1 + 3 * h ≤ ‖b i t‖) ∧
        (∀ t ∈ Icc (3 * h) (1 - 3 * h),
          ‖b i t‖ = 1 + 3 * h ↔ t = 3 * h ∨ t = 1 - 3 * h) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          ‖g i t‖ = 1 + 3 * h ↔ t = 0 ∨ t = 1)) ∧
      (∀ i,
        gamma i 0 = beta i (1 - 3 * h) ∧ gamma i 1 = beta i (3 * h) ∧
        (gamma i '' Icc (0 : ℝ) 1) ∩ (beta i '' Icc (3 * h) (1 - 3 * h)) =
          {beta i (3 * h), beta i (1 - 3 * h)} ∧
        gamma i (1 / 2) = kappa (J2.symm (0, sign i * (1 + h)))) ∧
      Disjoint (beta 0 '' Icc (0 : ℝ) 1) (beta 1 '' Icc (0 : ℝ) 1) ∧
      (∀ i, Disjoint (gamma i '' Icc (0 : ℝ) 1)
        (beta (other i) '' Icc (0 : ℝ) 1)) ∧
      ∀ i,
        Icc (-h / 16) (1 + h / 16) ×ˢ Icc (-w) w ⊆ (N i).source ∧
        (N i).source ⊆ U ×ˢ (univ : Set ℝ) ∧ (N i).target ⊆ kappa.target ∧
        ContDiffOn ℝ ∞ (N i) (N i).source ∧
        ContDiffOn ℝ ∞ (N i).symm (N i).target ∧
        ∀ p ∈ (N i).source,
          N i p = gamma i p.1 + p.2 • rot (deriv (gamma i) p.1) := by
  classical
  dsimp only
  let sigma : ℝ → ℝ := Real.smoothTransition
  let sign : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a => J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let other : Fin 2 → Fin 2 := Equiv.swap (0 : Fin 2) 1
  let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
  let K := kappa '' closedBall (0 : E2) 1
  let rb : ℝ → ℝ := fun t => 1 + 5 * h +
    (t - 5 * h) * (1 - sigma ((t - 4 * h) / (2 * h))) +
    (1 - t - 5 * h) * (1 - sigma ((1 - t - 4 * h) / (2 * h)))
  let ab : ℝ → ℝ := fun t => Real.pi / 4 +
    (Real.pi / 2) * sigma ((t - 4 * h) / (1 - 8 * h))
  let rg : ℝ → ℝ := fun t => 1 + h +
    (2 * h - t) * (1 - sigma ((t - h) / h)) +
    (2 * h - (1 - t)) * (1 - sigma ((1 - t - h) / h))
  let ag : ℝ → ℝ := fun t => 3 * Real.pi / 4 -
    (Real.pi / 2) * sigma ((t - h) / (1 - 2 * h))
  let b : Fin 2 → ℝ → E2 := fun i t => J2.symm
    (sign i * rb t * Real.cos (ab t), sign i * rb t * Real.sin (ab t))
  let g : Fin 2 → ℝ → E2 := fun i t => J2.symm
    (sign i * rg t * Real.cos (ag t), sign i * rg t * Real.sin (ag t))
  let beta : Fin 2 → ℝ → E2 := fun i => kappa ∘ b i
  let gamma : Fin 2 → ℝ → E2 := fun i => kappa ∘ g i
  let rot : E2 → E2 := fun v => J2.symm (-(J2 v).2, (J2 v).1)
  have hp := Real.pi_pos
  have h2 : 0 < 2 * h := by positivity
  have h8 : 0 < 1 - 8 * h := by linarith
  have h1 : 0 < 1 - 2 * h := by linarith
  have hU01 : Icc (0 : ℝ) 1 ⊆ U := by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hUmid : Icc (3 * h) (1 - 3 * h) ⊆ U := by
    intro t ht; exact hU01 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsig : ContDiff ℝ ∞ sigma := Real.smoothTransition.contDiff
  have hs0 (x : ℝ) (hx : x ≤ 0) : sigma x = 0 := Real.smoothTransition.zero_of_nonpos hx
  have hs1 (x : ℝ) (hx : 1 ≤ x) : sigma x = 1 := Real.smoothTransition.one_of_one_le hx
  have hsrange (x : ℝ) : 0 ≤ sigma x ∧ sigma x ≤ 1 :=
    ⟨Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x⟩
  have hsm : ContDiff ℝ ∞ rb ∧ ContDiff ℝ ∞ ab ∧
      ContDiff ℝ ∞ rg ∧ ContDiff ℝ ∞ ag := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [rb, ab, rg, ag] <;> fun_prop
  have hbref (t : ℝ) : rb (1 - t) = rb t := by
    dsimp only [rb]; rw [show 1 - (1 - t) = t by ring]; ring
  have hgref (t : ℝ) : rg (1 - t) = rg t := by
    dsimp only [rg]; rw [show 1 - (1 - t) = t by ring]; ring
  have hbL (t : ℝ) (ht : t ≤ 4 * h) : rb t = 1 + t := by
    have hr := hs1 ((1 - t - 4 * h) / (2 * h)) ((le_div_iff₀ h2).mpr (by linarith))
    have hl := hs0 ((t - 4 * h) / (2 * h)) ((div_le_iff₀ h2).mpr (by linarith))
    dsimp only [rb]; rw [hr, hl]; ring
  have hbR (t : ℝ) (ht : 1 - 4 * h ≤ t) : rb t = 2 - t := by
    rw [← hbref, hbL (1 - t) (by linarith)]; ring
  have hgL (t : ℝ) (ht : t ≤ h) : rg t = 1 + 3 * h - t := by
    have hr := hs1 ((1 - t - h) / h) ((le_div_iff₀ hh).mpr (by linarith))
    have hl := hs0 ((t - h) / h) ((div_le_iff₀ hh).mpr (by linarith))
    dsimp only [rg]; rw [hr, hl]; ring
  have hgR (t : ℝ) (ht : 1 - h ≤ t) : rg t = 1 + 3 * h + t - 1 := by
    rw [← hgref, hgL (1 - t) (by linarith)]; ring
  have hbT (t : ℝ) (ht : t ∈ Icc (4 * h) (6 * h)) :
      rb t ∈ Icc (1 + 4 * h) (1 + 6 * h) := by
    let q := sigma ((t - 4 * h) / (2 * h))
    have hq := hsrange ((t - 4 * h) / (2 * h))
    have he : rb t = (1 - q) * (1 + t) + q * (1 + 5 * h) := by
      have hr := hs1 ((1 - t - 4 * h) / (2 * h)) ((le_div_iff₀ h2).mpr (by linarith [ht.2]))
      dsimp [rb, q]; rw [hr]; ring
    rw [he]
    exact (convex_Icc (1 + 4 * h) (1 + 6 * h))
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith, by linarith⟩
      (sub_nonneg.mpr hq.2) hq.1 (by ring)
  have hgT (t : ℝ) (ht : t ∈ Icc h (2 * h)) : rg t ∈ Icc (1 + h) (1 + 2 * h) := by
    have hr := hs1 ((1 - t - h) / h) ((le_div_iff₀ hh).mpr (by linarith [ht.2]))
    have hq := hsrange ((t - h) / h)
    dsimp only [rg]; rw [hr]; constructor <;>
      nlinarith [ht.1, mul_nonneg (show 0 ≤ 2 * h - t by linarith [ht.2])
        (sub_nonneg.mpr hq.2), mul_nonneg (show 0 ≤ 2 * h - t by linarith [ht.2]) hq.1]
  have hbM (t : ℝ) (ht : t ∈ Icc (6 * h) (1 - 6 * h)) : rb t = 1 + 5 * h := by
    dsimp only [rb]
    rw [hs1 _ ((le_div_iff₀ h2).mpr (by linarith [ht.1])),
      hs1 _ ((le_div_iff₀ h2).mpr (by linarith [ht.2]))]; ring
  have hgM (t : ℝ) (ht : t ∈ Icc (2 * h) (1 - 2 * h)) : rg t = 1 + h := by
    dsimp only [rg]
    rw [hs1 _ ((le_div_iff₀ hh).mpr (by linarith [ht.1])),
      hs1 _ ((le_div_iff₀ hh).mpr (by linarith [ht.2]))]; ring
  have hbCases (t : ℝ) : (t ≤ 4 * h ∧ rb t = 1 + t) ∨
      (1 - 4 * h ≤ t ∧ rb t = 2 - t) ∨ rb t ∈ Icc (1 + 4 * h) (1 + 6 * h) := by
    by_cases hl : t ≤ 4 * h
    · exact Or.inl ⟨hl, hbL t hl⟩
    by_cases hr : 1 - 4 * h ≤ t
    · exact Or.inr (Or.inl ⟨hr, hbR t hr⟩)
    apply Or.inr ∘ Or.inr
    by_cases ht : t ≤ 6 * h
    · exact hbT t ⟨by linarith, ht⟩
    by_cases ht' : 1 - 6 * h ≤ t
    · rw [← hbref]; exact hbT (1 - t) ⟨by linarith, by linarith⟩
    rw [hbM t ⟨by linarith, by linarith⟩]; constructor <;> linarith
  have hgCases (t : ℝ) : (t ≤ h ∧ rg t = 1 + 3 * h - t) ∨
      (1 - h ≤ t ∧ rg t = 1 + 3 * h + t - 1) ∨ rg t ∈ Icc (1 + h) (1 + 2 * h) := by
    by_cases hl : t ≤ h
    · exact Or.inl ⟨hl, hgL t hl⟩
    by_cases hr : 1 - h ≤ t
    · exact Or.inr (Or.inl ⟨hr, hgR t hr⟩)
    apply Or.inr ∘ Or.inr
    by_cases ht : t ≤ 2 * h
    · exact hgT t ⟨by linarith, ht⟩
    by_cases ht' : 1 - 2 * h ≤ t
    · rw [← hgref]; exact hgT (1 - t) ⟨by linarith, by linarith⟩
    rw [hgM t ⟨by linarith, by linarith⟩]; exact ⟨le_rfl, by linarith⟩
  have hbBound (t : ℝ) (ht : t ∈ U) : 0 < rb t ∧ rb t < 2 := by
    rcases hbCases t with ⟨_, he⟩ | ⟨_, he⟩ | ⟨hlo, hhi⟩ <;> constructor <;> linarith [ht.1, ht.2]
  have hgBound (t : ℝ) (ht : t ∈ U) : 1 < rg t ∧ rg t < 2 := by
    rcases hgCases t with ⟨hl, he⟩ | ⟨hr, he⟩ | ⟨hlo, hhi⟩ <;> constructor <;> linarith [ht.1, ht.2]
  have hbClosed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 ≤ rb t ∧ rb t ≤ 1 + 6 * h := by
    rcases hbCases t with ⟨hl, he⟩ | ⟨hr, he⟩ | ⟨hlo, hhi⟩ <;> constructor <;> linarith [ht.1, ht.2]
  have hgClosed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 + h ≤ rg t ∧ rg t ≤ 1 + 3 * h := by
    rcases hgCases t with ⟨hl, he⟩ | ⟨hr, he⟩ | ⟨hlo, hhi⟩ <;> constructor <;> linarith [ht.1, ht.2]
  have hbOpen (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 1 < rb t := by
    rcases hbCases t with ⟨hl, he⟩ | ⟨hr, he⟩ | ⟨hlo, hhi⟩ <;> linarith [ht.1, ht.2]
  have hbCut (t : ℝ) (ht : t ∈ Icc (3 * h) (1 - 3 * h)) :
      1 + 3 * h ≤ rb t ∧ (rb t = 1 + 3 * h ↔ t = 3 * h ∨ t = 1 - 3 * h) := by
    constructor
    · rcases hbCases t with ⟨hl, he⟩ | ⟨hr, he⟩ | ⟨hlo, hhi⟩ <;> linarith [ht.1, ht.2]
    constructor
    · intro he; rcases hbCases t with ⟨hl, he'⟩ | ⟨hr, he'⟩ | he'
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exfalso; linarith [he'.1]
    · rintro (rfl | rfl)
      · rw [hbL _ (by linarith)]
      · rw [hbR _ (by linarith)]; ring
  have hgCut (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      rg t = 1 + 3 * h ↔ t = 0 ∨ t = 1 := by
    constructor
    · intro he; rcases hgCases t with ⟨hl, he'⟩ | ⟨hr, he'⟩ | he'
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exfalso; linarith [he'.2]
    · rintro (rfl | rfl)
      · rw [hgL _ (by linarith)]; ring
      · rw [hgR _ (by linarith)]; ring
  have haBounds (t : ℝ) : ab t ∈ Icc (Real.pi / 4) (3 * Real.pi / 4) ∧
      ag t ∈ Icc (Real.pi / 4) (3 * Real.pi / 4) := by
    have hb0 := mul_nonneg (half_pos hp).le (hsrange ((t - 4 * h) / (1 - 8 * h))).1
    have hb1 := mul_le_mul_of_nonneg_left (hsrange ((t - 4 * h) / (1 - 8 * h))).2 (half_pos hp).le
    have hg0 := mul_nonneg (half_pos hp).le (hsrange ((t - h) / (1 - 2 * h))).1
    have hg1 := mul_le_mul_of_nonneg_left (hsrange ((t - h) / (1 - 2 * h))).2 (half_pos hp).le
    dsimp only [ab, ag]; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have habL (t : ℝ) (ht : t ≤ 4 * h) : ab t = Real.pi / 4 := by
    dsimp only [ab]; rw [hs0 _ ((div_le_iff₀ h8).mpr (by linarith))]; ring
  have habR (t : ℝ) (ht : 1 - 4 * h ≤ t) : ab t = 3 * Real.pi / 4 := by
    dsimp only [ab]; rw [hs1 _ ((le_div_iff₀ h8).mpr (by linarith))]; ring
  have hagL (t : ℝ) (ht : t ≤ h) : ag t = 3 * Real.pi / 4 := by
    dsimp only [ag]; rw [hs0 _ ((div_le_iff₀ h1).mpr (by linarith))]; ring
  have hagR (t : ℝ) (ht : 1 - h ≤ t) : ag t = Real.pi / 4 := by
    dsimp only [ag]; rw [hs1 _ ((le_div_iff₀ h1).mpr (by linarith))]; ring
  have hsigFiber (x y : ℝ) (he : sigma x = sigma y) :
      (x ≤ 0 ∧ y ≤ 0) ∨ (1 ≤ x ∧ 1 ≤ y) ∨ x = y := by
    by_cases hx : x ≤ 0
    · exact Or.inl ⟨hx, Real.smoothTransition.zero_iff_nonpos.mp (he.symm.trans (hs0 x hx))⟩
    by_cases hx' : 1 ≤ x
    · exact Or.inr (Or.inl
        ⟨hx', Real.smoothTransition.eq_one_iff_one_le.mp (he.symm.trans (hs1 x hx'))⟩)
    have hy : 0 < y := by
      by_contra hy; have hz := hs0 y (le_of_not_gt hy)
      have hz' := Real.smoothTransition.pos_of_pos (lt_of_not_ge hx)
      change 0 < sigma x at hz'
      rw [he, hz] at hz'; exact lt_irrefl _ hz'
    have hy' : y < 1 := by
      by_contra hy'; have hz := hs1 y (le_of_not_gt hy')
      have hz' := Real.smoothTransition.lt_one_of_lt_one (lt_of_not_ge hx')
      change sigma x < 1 at hz'
      rw [he, hz] at hz'; exact lt_irrefl _ hz'
    exact Or.inr (Or.inr (saddle_smoothTransition_regular.2.injOn
      ⟨le_of_not_ge hx, le_of_not_ge hx'⟩ ⟨hy.le, hy'.le⟩ he))
  have hbPair (s t : ℝ) (hr : rb s = rb t) (ha : ab s = ab t) : s = t := by
    have he : sigma ((s - 4 * h) / (1 - 8 * h)) = sigma ((t - 4 * h) / (1 - 8 * h)) :=
      (mul_left_cancel₀ (half_pos hp).ne' (add_left_cancel ha))
    rcases hsigFiber _ _ he with ⟨hs, ht⟩ | ⟨hs, ht⟩ | he
    · rw [hbL s (by have := (div_le_iff₀ h8).mp hs; linarith),
        hbL t (by have := (div_le_iff₀ h8).mp ht; linarith)] at hr; linarith
    · rw [hbR s (by have := (le_div_iff₀ h8).mp hs; linarith),
        hbR t (by have := (le_div_iff₀ h8).mp ht; linarith)] at hr; linarith
    · have he' := (div_left_inj' h8.ne').mp he; linarith
  have hgPair (s t : ℝ) (hr : rg s = rg t) (ha : ag s = ag t) : s = t := by
    have he : sigma ((s - h) / (1 - 2 * h)) = sigma ((t - h) / (1 - 2 * h)) := by
      apply mul_left_cancel₀ (half_pos hp).ne'; dsimp only [ag] at ha; linarith
    rcases hsigFiber _ _ he with ⟨hs, ht⟩ | ⟨hs, ht⟩ | he
    · rw [hgL s (by have := (div_le_iff₀ h1).mp hs; linarith),
        hgL t (by have := (div_le_iff₀ h1).mp ht; linarith)] at hr; linarith
    · rw [hgR s (by have := (le_div_iff₀ h1).mp hs; linarith),
        hgR t (by have := (le_div_iff₀ h1).mp ht; linarith)] at hr; linarith
    · have he' := (div_left_inj' h1.ne').mp he; linarith
  have hleftD (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a c v : ℝ)
      (he : ∀ t ≤ a, f t = c + v * t) (t : ℝ) (ht : t ≤ a) : deriv f t = v := by
    have hl : HasDerivAt (fun s : ℝ => c + v * s) v t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul v).const_add c
    exact (uniqueDiffOn_Iic a t ht).eq_deriv _
      ((hf.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt)
      (hl.hasDerivWithinAt.congr_of_mem he ht)
  have hrightD (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a c v : ℝ)
      (he : ∀ t, a ≤ t → f t = c + v * t) (t : ℝ) (ht : a ≤ t) : deriv f t = v := by
    have hl : HasDerivAt (fun s : ℝ => c + v * s) v t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul v).const_add c
    exact (uniqueDiffOn_Ici a t ht).eq_deriv _
      ((hf.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt)
      (hl.hasDerivWithinAt.congr_of_mem he ht)
  have hbJet (t : ℝ) : deriv rb t ≠ 0 ∨ deriv ab t ≠ 0 := by
    by_cases hl : t ≤ 4 * h
    · exact Or.inl (by rw [hleftD rb hsm.1 (4 * h) 1 1
        (fun s hs => by simpa using hbL s hs) t hl]; norm_num)
    by_cases hr : 1 - 4 * h ≤ t
    · exact Or.inl (by rw [hrightD rb hsm.1 (1 - 4 * h) 2 (-1)
        (fun s hs => by simpa [sub_eq_add_neg] using hbR s hs) t hr]; norm_num)
    have hd : HasDerivAt ab
        (Real.pi / 2 * (deriv sigma ((t - 4 * h) / (1 - 8 * h)) * (1 / (1 - 8 * h)))) t :=
      (((hsig.differentiable (by simp) _).hasDerivAt.comp t
        (((hasDerivAt_id t).sub_const (4 * h)).div_const (1 - 8 * h))).const_mul
          (Real.pi / 2)).const_add (Real.pi / 4)
    have hv := saddle_smoothTransition_regular.1 ((t - 4 * h) / (1 - 8 * h))
      ⟨div_pos (by linarith) h8, (div_lt_one h8).mpr (by linarith)⟩
    apply Or.inr
    rw [hd.deriv]; exact (mul_pos (half_pos hp) (mul_pos hv (one_div_pos.mpr h8))).ne'
  have hgJet (t : ℝ) : deriv rg t ≠ 0 ∨ deriv ag t ≠ 0 := by
    by_cases hl : t ≤ h
    · exact Or.inl (by rw [hleftD rg hsm.2.2.1 h (1 + 3 * h) (-1)
        (fun s hs => by simpa [sub_eq_add_neg] using hgL s hs) t hl]; norm_num)
    by_cases hr : 1 - h ≤ t
    · exact Or.inl (by rw [hrightD rg hsm.2.2.1 (1 - h) (3 * h) 1
        (fun s hs => by rw [hgR s hs]; ring) t hr]; norm_num)
    have hd : HasDerivAt ag
        (-(Real.pi / 2 * (deriv sigma ((t - h) / (1 - 2 * h)) * (1 / (1 - 2 * h))))) t :=
      (((hsig.differentiable (by simp) _).hasDerivAt.comp t
        (((hasDerivAt_id t).sub_const h).div_const (1 - 2 * h))).const_mul
          (Real.pi / 2)).const_sub (3 * Real.pi / 4)
    have hv := saddle_smoothTransition_regular.1 ((t - h) / (1 - 2 * h))
      ⟨div_pos (by linarith) h1, (div_lt_one h1).mpr (by linarith)⟩
    apply Or.inr
    rw [hd.deriv]
    exact neg_ne_zero.mpr (mul_pos (half_pos hp) (mul_pos hv (one_div_pos.mpr h1))).ne'
  have hsign (i : Fin 2) : sign i ^ 2 = 1 ∧ sign i ≠ 0 ∧ |sign i| = 1 := by
    fin_cases i <;> norm_num [sign]
  have hpolar (R A : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (hA : ContDiff ℝ ∞ A)
      (hbound : ∀ t ∈ U, 0 < R t ∧ R t < 2)
      (ha : ∀ t, A t ∈ Icc (Real.pi / 4) (3 * Real.pi / 4))
      (hpair : ∀ s t, R s = R t → A s = A t → s = t)
      (hjet : ∀ t, deriv R t ≠ 0 ∨ deriv A t ≠ 0) (i : Fin 2) :
      let v : ℝ → E2 := fun t => J2.symm
        (sign i * R t * Real.cos (A t), sign i * R t * Real.sin (A t))
      ContDiff ℝ ∞ v ∧ (∀ t ∈ U, ‖v t‖ = R t) ∧
      ContDiffOn ℝ ∞ (kappa ∘ v) U ∧ InjOn (kappa ∘ v) U ∧
      ∀ t ∈ U, deriv (kappa ∘ v) t ≠ 0 := by
    let v : ℝ → E2 := fun t => J2.symm
      (sign i * R t * Real.cos (A t), sign i * R t * Real.sin (A t))
    have hv : ContDiff ℝ ∞ v := by dsimp [v]; fun_prop
    have hn (t : ℝ) (ht : t ∈ U) : ‖v t‖ = R t := by
      have he : ‖v t‖ ^ 2 = R t ^ 2 := by
        calc
          ‖v t‖ ^ 2 = sign i ^ 2 * R t ^ 2 * (Real.sin (A t) ^ 2 + Real.cos (A t) ^ 2) := by
            rw [← hJ2]; dsimp [v]; simp only [J2.apply_symm_apply]; ring
          _ = R t ^ 2 := by rw [(hsign i).1, Real.sin_sq_add_cos_sq]; ring
      nlinarith [norm_nonneg (v t), (hbound t ht).1]
    have hsource (t : ℝ) (ht : t ∈ U) : v t ∈ kappa.source :=
      hkappaSource (mem_closedBall_zero_iff.mpr (by rw [hn t ht]; exact (hbound t ht).2.le))
    have hinj : InjOn v U := by
      intro s hs t ht he
      have hr : R s = R t := (hn s hs).symm.trans ((congrArg norm he).trans (hn t ht))
      have hc : Real.cos (A s) = Real.cos (A t) := by
        have hx := congrArg (fun x : E2 => (J2 x).1) he
        dsimp [v] at hx; simp only [J2.apply_symm_apply] at hx
        rw [← hr] at hx
        exact mul_left_cancel₀ (mul_ne_zero (hsign i).2.1 (hbound s hs).1.ne') hx
      exact hpair s t hr (Real.injOn_cos
        ⟨by linarith [(ha s).1], by linarith [(ha s).2]⟩
        ⟨by linarith [(ha t).1], by linarith [(ha t).2]⟩ hc)
    have hreg (t : ℝ) (ht : t ∈ U) : deriv v t ≠ 0 := by
      let r' := deriv R t
      let a' := deriv A t
      let X := r' * Real.cos (A t) - R t * a' * Real.sin (A t)
      let Y := r' * Real.sin (A t) + R t * a' * Real.cos (A t)
      have hr := (hR.differentiable (by simp) t).hasDerivAt
      have ha' := (hA.differentiable (by simp) t).hasDerivAt
      have hd : HasDerivAt v (J2.symm (sign i * X, sign i * Y)) t := by
        have hdPair : HasDerivAt
            (fun s => (sign i * R s * Real.cos (A s), sign i * R s * Real.sin (A s)))
            (sign i * X, sign i * Y) t := by
          convert! (((hr.const_mul (sign i)).mul ha'.cos).prodMk
            ((hr.const_mul (sign i)).mul ha'.sin)) using 1
          apply Prod.ext <;> dsimp [X, Y, r', a'] <;> ring
        exact (J2.symm : (ℝ × ℝ) →L[ℝ] E2).hasFDerivAt.comp_hasDerivAt t hdPair
      intro he
      rw [hd.deriv] at he
      have hX : X = 0 := by
        apply mul_left_cancel₀ (hsign i).2.1
        simpa only [J2.apply_symm_apply, map_zero, Prod.fst_zero, mul_zero] using
          congrArg (fun x : E2 => (J2 x).1) he
      have hY : Y = 0 := by
        apply mul_left_cancel₀ (hsign i).2.1
        simpa only [J2.apply_symm_apply, map_zero, Prod.snd_zero, mul_zero] using
          congrArg (fun x : E2 => (J2 x).2) he
      have hr0 : r' = 0 := by
        calc
          r' = r' * (Real.sin (A t) ^ 2 + Real.cos (A t) ^ 2) := by
            rw [Real.sin_sq_add_cos_sq, mul_one]
          _ = Real.cos (A t) * X + Real.sin (A t) * Y := by dsimp [X, Y]; ring
          _ = 0 := by rw [hX, hY]; ring
      have hra0 : R t * a' = 0 := by
        calc
          R t * a' = R t * a' * (Real.sin (A t) ^ 2 + Real.cos (A t) ^ 2) := by
            rw [Real.sin_sq_add_cos_sq, mul_one]
          _ = -Real.sin (A t) * X + Real.cos (A t) * Y := by dsimp [X, Y]; ring
          _ = 0 := by rw [hX, hY]; ring
      rcases hjet t with hrn | han
      · exact hrn hr0
      · exact han ((mul_eq_zero.mp hra0).resolve_left (hbound t ht).1.ne')
    refine ⟨hv, hn, hkappa.comp hv.contDiffOn hsource,
      fun s hs t ht he => hinj hs ht (kappa.injOn (hsource s hs) (hsource t ht) he), ?_⟩
    intro t ht
    obtain ⟨L, hL⟩ := exists_smoothChart_derivative kappa hkappa hkappaInv (hsource t ht)
    have hd : HasDerivAt (kappa ∘ v) (L (deriv v t)) t :=
      hL.comp_hasDerivAt t (hv.differentiable (by simp) t).hasDerivAt
    intro he
    change deriv (kappa ∘ v) t = 0 at he
    rw [hd.deriv] at he
    have he' : L (deriv v t) = L 0 := by simpa only [map_zero] using he
    exact hreg t ht (L.injective he')
  have hB (i : Fin 2) := hpolar rb ab hsm.1 hsm.2.1 hbBound
    (fun t => (haBounds t).1) hbPair hbJet i
  have hG (i : Fin 2) := hpolar rg ag hsm.2.2.1 hsm.2.2.2
    (fun t ht => ⟨lt_trans zero_lt_one (hgBound t ht).1, (hgBound t ht).2⟩)
    (fun t => (haBounds t).2) hgPair hgJet i
  have hbSource (i : Fin 2) (t : ℝ) (ht : t ∈ U) : b i t ∈ kappa.source :=
    hkappaSource (mem_closedBall_zero_iff.mpr (by rw [(hB i).2.1 t ht]; exact (hbBound t ht).2.le))
  have hgSource (i : Fin 2) (t : ℝ) (ht : t ∈ U) : g i t ∈ kappa.source :=
    hkappaSource (mem_closedBall_zero_iff.mpr (by rw [(hG i).2.1 t ht]; exact (hgBound t ht).2.le))
  have hsector (a : ℝ) (ha : a ∈ Icc (Real.pi / 4) (3 * Real.pi / 4)) :
      0 < Real.sin a ∧ |Real.cos a| ≤ Real.sin a := by
    have hs : 0 < Real.sin a :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.1]) (by linarith [ha.2])
    have hplus := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ a + Real.pi / 4 by linarith [ha.1])
      (show a + Real.pi / 4 ≤ Real.pi by linarith [ha.2])
    have hminus := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ a - Real.pi / 4 by linarith [ha.1])
      (show a - Real.pi / 4 ≤ Real.pi by linarith [ha.2])
    rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four] at hplus
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four] at hminus
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hplus' : 0 ≤ Real.sin a + Real.cos a := nonneg_of_mul_nonneg_left
      (show 0 ≤ (Real.sin a + Real.cos a) * (Real.sqrt 2 / 2) by nlinarith [hplus])
      (half_pos hsqrt)
    have hminus' : 0 ≤ Real.sin a - Real.cos a := nonneg_of_mul_nonneg_left
      (show 0 ≤ (Real.sin a - Real.cos a) * (Real.sqrt 2 / 2) by nlinarith [hminus])
      (half_pos hsqrt)
    exact ⟨hs, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hpolarSector (i : Fin 2) (r a : ℝ) (hr : 0 < r)
      (ha : a ∈ Icc (Real.pi / 4) (3 * Real.pi / 4)) :
      let x := J2.symm (sign i * r * Real.cos a, sign i * r * Real.sin a)
      0 < sign i * (J2 x).2 ∧ |(J2 x).1| ≤ sign i * (J2 x).2 := by
    dsimp only; simp only [J2.apply_symm_apply]
    have hs := hsector a ha
    have he : sign i * (sign i * r * Real.sin a) = r * Real.sin a := by
      calc
        _ = sign i ^ 2 * (r * Real.sin a) := by ring
        _ = r * Real.sin a := by rw [(hsign i).1, one_mul]
    rw [he, abs_mul, abs_mul, (hsign i).2.2, abs_of_pos hr, one_mul]
    exact ⟨mul_pos hr hs.1, mul_le_mul_of_nonneg_left hs.2 hr.le⟩
  have hbSector (i : Fin 2) (t : ℝ) (ht : t ∈ U) :
      0 < sign i * (J2 (b i t)).2 ∧ |(J2 (b i t)).1| ≤ sign i * (J2 (b i t)).2 :=
    hpolarSector i (rb t) (ab t) (hbBound t ht).1 (haBounds t).1
  have hgSector (i : Fin 2) (t : ℝ) (ht : t ∈ U) :
      0 < sign i * (J2 (g i t)).2 ∧ |(J2 (g i t)).1| ≤ sign i * (J2 (g i t)).2 :=
    hpolarSector i (rg t) (ag t) (lt_trans zero_lt_one (hgBound t ht).1) (haBounds t).2
  have hsqrt : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    apply (div_eq_div_iff (by norm_num) (Real.sqrt_pos.mpr (by norm_num)).ne').mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hcos3 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
  have hsin3 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_four]
  have hp0 (i : Fin 2) (r : ℝ) : J2.symm
      (sign i * r * Real.cos (Real.pi / 4), sign i * r * Real.sin (Real.pi / 4)) =
        r • port (ep (i, 0)) := by
    apply J2.injective
    fin_cases i <;> apply Prod.ext <;>
      norm_num [port, ep, finProdFinEquiv, sx, sy, sign, Real.cos_pi_div_four,
        Real.sin_pi_div_four, hsqrt, map_smul] <;> ring
  have hp1 (i : Fin 2) (r : ℝ) : J2.symm
      (sign i * r * Real.cos (3 * Real.pi / 4), sign i * r * Real.sin (3 * Real.pi / 4)) =
        r • port (ep (i, 1)) := by
    apply J2.injective
    fin_cases i <;> apply Prod.ext <;>
      norm_num [port, ep, finProdFinEquiv, sx, sy, sign, hcos3, hsin3, hsqrt, map_smul] <;> ring
  have hbEnds (i : Fin 2) (t : ℝ) :
      (t ≤ 4 * h → beta i t = kappa ((1 + t) • port (ep (i, 0)))) ∧
      (1 - 4 * h ≤ t → beta i t = kappa ((2 - t) • port (ep (i, 1)))) := by
    constructor
    · intro ht; dsimp only [beta, Function.comp_apply, b]; rw [hbL t ht, habL t ht, hp0]
    · intro ht; dsimp only [beta, Function.comp_apply, b]; rw [hbR t ht, habR t ht, hp1]
  have hgEnds (i : Fin 2) (t : ℝ) :
      (t ≤ h → gamma i t = kappa ((1 + 3 * h - t) • port (ep (i, 1)))) ∧
      (1 - h ≤ t → gamma i t = kappa ((1 + 3 * h + t - 1) • port (ep (i, 0)))) := by
    constructor
    · intro ht; dsimp only [gamma, Function.comp_apply, g]; rw [hgL t ht, hagL t ht, hp1]
    · intro ht; dsimp only [gamma, Function.comp_apply, g]; rw [hgR t ht, hagR t ht, hp0]
  have hjoin (i : Fin 2) : gamma i 0 = beta i (1 - 3 * h) ∧ gamma i 1 = beta i (3 * h) := by
    constructor
    · rw [(hgEnds i 0).1 (by linarith), (hbEnds i (1 - 3 * h)).2 (by linarith)]
      congr 2
      ring
    · rw [(hgEnds i 1).2 (by linarith), (hbEnds i (3 * h)).1 (by linarith)]
      congr 2
      ring
  have hout (x : E2) (hx : x ∈ kappa.source) (hn : 1 < ‖x‖) : kappa x ∈ Kᶜ := by
    rintro ⟨y, hy, he⟩
    have hys : y ∈ kappa.source := hkappaSource (mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hy).trans (by norm_num)))
    have hyx := kappa.injOn hys hx he
    rw [hyx] at hy
    exact (not_le_of_gt hn) (mem_closedBall_zero_iff.mp hy)
  have hinter (i : Fin 2) :
      (gamma i '' Icc (0 : ℝ) 1) ∩ (beta i '' Icc (3 * h) (1 - 3 * h)) =
        {beta i (3 * h), beta i (1 - 3 * h)} := by
    ext y; simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, t, ht, he⟩
      have hn := congrArg norm (kappa.injOn (hbSource i t (hUmid ht)) (hgSource i s (hU01 hs)) he)
      rw [(hB i).2.1 t (hUmid ht), (hG i).2.1 s (hU01 hs)] at hn
      have ht' := (hbCut t ht).2.mp (by linarith [(hbCut t ht).1, (hgClosed s hs).2])
      rcases ht' with rfl | rfl
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · rintro (rfl | rfl)
      · exact ⟨⟨1, by norm_num, (hjoin i).2⟩, 3 * h, ⟨le_rfl, by linarith⟩, rfl⟩
      · exact ⟨⟨0, by norm_num, (hjoin i).1⟩, 1 - 3 * h, ⟨by linarith, le_rfl⟩, rfl⟩
  have hhalf : sigma (1 / 2) = 1 / 2 := by
    dsimp only [sigma, Real.smoothTransition]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    have hn := (expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).ne'
    field_simp [hn]; ring
  have hmid (i : Fin 2) : gamma i (1 / 2) = kappa (J2.symm (0, sign i * (1 + h))) := by
    have hr := hgM (1 / 2) ⟨by linarith, by linarith⟩
    have ha : ag (1 / 2) = Real.pi / 2 := by
      dsimp only [ag]
      rw [show ((1 : ℝ) / 2 - h) / (1 - 2 * h) = 1 / 2 by field_simp [h1.ne'], hhalf]
      ring
    simp only [gamma, Function.comp_apply, g, hr, ha, Real.cos_pi_div_two,
      Real.sin_pi_div_two, mul_zero, mul_one]
  have hopposite (i : Fin 2) (x y : E2) (hx : x ∈ kappa.source) (hy : y ∈ kappa.source)
      (hsx : 0 < sign i * (J2 x).2) (hsy : 0 < sign (other i) * (J2 y).2) : kappa x ≠ kappa y := by
    intro he
    have hh' := congrArg (fun z : E2 => (J2 z).2) (kappa.injOn hx hy he)
    fin_cases i <;> norm_num [sign, other] at hsx hsy <;> linarith
  have hbb : Disjoint (beta 0 '' Icc (0 : ℝ) 1) (beta 1 '' Icc (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    exact hopposite 0 (b 0 s) (b 1 t) (hbSource 0 s (hU01 hs)) (hbSource 1 t (hU01 ht))
      (hbSector 0 s (hU01 hs)).1 (by simpa [other] using (hbSector 1 t (hU01 ht)).1) he.symm
  have hgb (i : Fin 2) : Disjoint (gamma i '' Icc (0 : ℝ) 1)
      (beta (other i) '' Icc (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    exact hopposite i (g i s) (b (other i) t)
      (hgSource i s (hU01 hs)) (hbSource (other i) t (hU01 ht))
      (hgSector i s (hU01 hs)).1 (hbSector (other i) t (hU01 ht)).1 he.symm
  have hbuf : Icc (-h / 16) (1 + h / 16) ⊆ U := by
    intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hNC (i : Fin 2) := exists_saddle_planar_curve_normal_chart J2 (gamma i)
    (-h / 8) (1 + h / 8) (-h / 16) (1 + h / 16)
    (by linarith) (by linarith) (by linarith)
    (hG i).2.2.1 (hG i).2.2.2.1 (hG i).2.2.2.2 kappa.target kappa.open_target
    (by rintro y ⟨t, ht, rfl⟩; exact kappa.map_source (hgSource i t (hbuf ht)))
  choose wi N hwi hNs hNV hNt hNsm hNinv hNpoint using hNC
  let w := min (wi 0) (wi 1)
  have hw : 0 < w := lt_min (hwi 0) (hwi 1)
  have hww (i : Fin 2) : w ≤ wi i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  refine ⟨w, N, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbb, hgb, ?_⟩
  · intro i; exact ⟨(hB i).1, (hG i).1⟩
  · intro i t ht; exact ⟨(hB i).2.1 t ht, (hbBound t ht).1, (hbBound t ht).2,
      (hG i).2.1 t ht, (hgBound t ht).1, (hgBound t ht).2⟩
  · intro i; exact ⟨(hB i).2.2.1, (hB i).2.2.2.1, (hB i).2.2.2.2,
      (hG i).2.2.1, (hG i).2.2.2.1, (hG i).2.2.2.2⟩
  · intro i t _ht; exact ⟨(hbEnds i t).1, (hbEnds i t).2, (hgEnds i t).1, (hgEnds i t).2⟩
  · intro i; constructor
    · intro t ht; change 1 ≤ ‖b i t‖ ∧ ‖b i t‖ ≤ 1 + 6 * h ∧ _
      rw [(hB i).2.1 t (hU01 ht)]
      exact ⟨(hbClosed t ht).1, (hbClosed t ht).2, (hbSector i t (hU01 ht)).2⟩
    · intro t ht; change 1 + h ≤ ‖g i t‖ ∧ ‖g i t‖ ≤ 1 + 3 * h ∧ _
      rw [(hG i).2.1 t (hU01 ht)]
      exact ⟨(hgClosed t ht).1, (hgClosed t ht).2, (hgSector i t (hU01 ht)).2⟩
  · intro i; refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro y ⟨t, ht, rfl⟩
      exact hout (b i t) (hbSource i t (hU01 ⟨ht.1.le, ht.2.le⟩))
        (by rw [(hB i).2.1 t (hU01 ⟨ht.1.le, ht.2.le⟩)]; exact hbOpen t ht)
    · rintro y ⟨t, ht, rfl⟩
      exact hout (g i t) (hgSource i t ht) (by rw [(hG i).2.1 t ht]; exact (hgBound t ht).1)
    · intro t ht; rw [(hB i).2.1 t (hUmid ht)]; exact (hbCut t ht).1
    · intro t ht; rw [(hB i).2.1 t (hUmid ht)]; exact (hbCut t ht).2
    · intro t ht; rw [(hG i).2.1 t (hU01 ht)]; exact hgCut t ht
  · intro i; exact ⟨(hjoin i).1, (hjoin i).2, hinter i, hmid i⟩
  · intro i; refine ⟨?_, hNV i, hNt i, hNsm i, hNinv i, hNpoint i⟩
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    exact hNs i ⟨ht, ⟨by linarith [(hww i), hs.1], by linarith [(hww i), hs.2]⟩⟩

end PoincareConjecture.M25.Topology3D
