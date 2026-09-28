import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option linter.unusedVariables false in

theorem saddle_selected_level_gluing
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (c rho delta : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (kp : OpenPartialHomeomorph E2 E2)
    (hksSource : closedBall (0 : E2) 2 ⊆ ks.source)
    (hkpSource : closedBall (0 : E2) 2 ⊆ kp.source)
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hFNorm : ∀ t x, ‖F t x‖ = ‖x‖) :
    let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let sigma : ℝ → ℝ := Real.smoothTransition
    let K := kp '' closedBall (0 : E2) 1
    let V := kp '' ball (0 : E2) 1
    let Cs := ks '' closedBall (0 : E2) 1
    let Vs := ks '' ball (0 : E2) 1
    let Elevel : ℝ → Set E3 := fun z => (S ∩ {y | H y = c + z}) \ (j '' Vs)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let X : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
      (sx i * Real.sqrt ((r ^ 2 + a) / 2),
        sy i * Real.sqrt ((r ^ 2 - a) / 2))
    ∀ (hCoordinates : ∀ x ∈ closedBall (0 : E2) 2,
        pi (j (ks x)) = kp x ∧
        H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))
      (hNoSheets : ∀ z : ℝ, |z| ≤ 2 * delta → ∀ p : UnitTwoSphere,
        H (j p) = c + z →
        (pi (j p) ∈ V ↔ p ∈ Vs) ∧ (pi (j p) ∈ K ↔ p ∈ Cs))
      (hExterior : ∀ tau ∈ Icc (0 : ℝ) delta,
        Phi tau '' Elevel (-delta) = Elevel (-delta + tau))
      (hNative : ∀ tau ∈ Icc (0 : ℝ) delta, ∀ i : Fin 4,
        ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
          Phi tau (j (ks (X (-delta / rho ^ 2) (1 + a) i))) =
            j (ks (X ((-delta + tau) / rho ^ 2) (1 + a) i)))
      (hAngular : ∀ t : ℝ, ∀ i : Fin 4,
        ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
          F t (X (-delta / rho ^ 2) (1 + a) i) =
            X ((-delta + sigma t * delta) / rho ^ 2) (1 + a) i),
    let N : Set UnitTwoSphere := {p | H (j p) = c - delta}
    let A : ℝ → UnitTwoSphere → E2 := fun t p =>
      @ite E2 (p ∈ Vs) (Classical.propDecidable _)
        (kp (F t (ks.symm p)))
        (pi (Phi (sigma t * delta) (j p)))
    (∀ t : ℝ, Set.InjOn (A t) N) ∧
    (∀ t : ℝ, ∀ p ∈ N,
      (A t p ∈ V ↔ p ∈ Vs) ∧
      (A t p ∈ K ↔ p ∈ Cs) ∧
      (p ∈ Cs → A t p = kp (F t (ks.symm p))) ∧
      (p ∉ Vs → A t p = pi (Phi (sigma t * delta) (j p)))) ∧
    (∀ t : ℝ, ∀ p ∈ N, p ∈ ks.target →
      7 / 8 < ‖ks.symm p‖ → ‖ks.symm p‖ < 9 / 8 →
        kp (F t (ks.symm p)) = pi (Phi (sigma t * delta) (j p))) ∧
    (∀ t : ℝ, (A t '' N) \ V =
      {x : E2 | L.symm (x, c - delta + sigma t * delta) ∈ S} \ V) ∧
    (∀ t : ℝ, (A t '' N) ∩ K =
      kp '' ((F t) '' {x : E2 | ‖x‖ ≤ 1 ∧
        rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = -delta})) := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S := range j
  let sigma : ℝ → ℝ := Real.smoothTransition
  let K := kp '' closedBall (0 : E2) 1
  let V := kp '' ball (0 : E2) 1
  let Cs := ks '' closedBall (0 : E2) 1
  let Vs := ks '' ball (0 : E2) 1
  let Elevel : ℝ → Set E3 := fun z => (S ∩ {y | H y = c + z}) \ (j '' Vs)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let X : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
    (sx i * Real.sqrt ((r ^ 2 + a) / 2),
      sy i * Real.sqrt ((r ^ 2 - a) / 2))
  dsimp only
  intro hCoordinates hNoSheets hExterior hNative hAngular
  change ∀ x ∈ closedBall (0 : E2) 2,
    pi (j (ks x)) = kp x ∧
      H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) at hCoordinates
  change ∀ z : ℝ, |z| ≤ 2 * delta → ∀ p : UnitTwoSphere,
    H (j p) = c + z →
      (pi (j p) ∈ V ↔ p ∈ Vs) ∧ (pi (j p) ∈ K ↔ p ∈ Cs) at hNoSheets
  change ∀ tau ∈ Icc (0 : ℝ) delta,
    Phi tau '' Elevel (-delta) = Elevel (-delta + tau) at hExterior
  change ∀ tau ∈ Icc (0 : ℝ) delta, ∀ i : Fin 4,
    ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
      Phi tau (j (ks (X (-delta / rho ^ 2) (1 + a) i))) =
        j (ks (X ((-delta + tau) / rho ^ 2) (1 + a) i)) at hNative
  change ∀ t : ℝ, ∀ i : Fin 4, ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
    F t (X (-delta / rho ^ 2) (1 + a) i) =
      X ((-delta + sigma t * delta) / rho ^ 2) (1 + a) i at hAngular
  let N : Set UnitTwoSphere := {p | H (j p) = c - delta}
  let A : ℝ → UnitTwoSphere → E2 := fun t p =>
    if p ∈ Vs then kp (F t (ks.symm p)) else pi (Phi (sigma t * delta) (j p))
  have hr2 : 0 < rho ^ 2 := pow_pos hrho 2
  have hrne : rho ^ 2 ≠ 0 := ne_of_gt hr2
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1 (x₁ := (p, 0)) (x₂ := (q, 0))
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have htime (t : ℝ) : sigma t * delta ∈ Icc (0 : ℝ) delta :=
    ⟨mul_nonneg (Real.smoothTransition.nonneg t) hdelta.le,
      (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) hdelta.le).trans_eq
        (one_mul delta)⟩
  have hnew (t : ℝ) : |-delta + sigma t * delta| ≤ 2 * delta :=
    abs_le.mpr ⟨by linarith [(htime t).1], by linarith [(htime t).2]⟩
  have hs2 {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ ks.source :=
    hksSource (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hp2 {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kp.source :=
    hkpSource (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hsc {p : UnitTwoSphere} (hp : p ∈ Cs) :
      p ∈ ks.target ∧ ‖ks.symm p‖ ≤ 1 := by
    obtain ⟨x, hx, rfl⟩ := hp
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hxs := hs2 (by linarith)
    exact ⟨ks.map_source hxs, by simpa only [ks.left_inv hxs] using hn⟩
  have hsv {p : UnitTwoSphere} (hp : p ∈ Vs) :
      p ∈ ks.target ∧ ‖ks.symm p‖ < 1 := by
    obtain ⟨x, hx, rfl⟩ := hp
    have hn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hxs := hs2 (by linarith)
    exact ⟨ks.map_source hxs, by simpa only [ks.left_inv hxs] using hn⟩
  have hVsCs : Vs ⊆ Cs := image_mono ball_subset_closedBall
  have hrim {p : UnitTwoSphere} (hc : p ∈ Cs) (hv : p ∉ Vs) : ‖ks.symm p‖ = 1 := by
    have hp := hsc hc
    apply le_antisymm hp.2
    by_contra hn
    exact hv ⟨ks.symm p,
      by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hn,
      ks.right_inv hp.1⟩
  have hzsmall (z : ℝ) (hz : |z| ≤ delta) : |z / rho ^ 2| ≤ 1 / 128 := by
    rw [abs_div, abs_of_pos hr2]
    apply (div_le_iff₀ hr2).mpr
    nlinarith
  have hSigns (i : Fin 4) : (sx i) ^ 2 = 1 ∧ (sy i) ^ 2 = 1 := by
    fin_cases i <;> norm_num [sx, sy]
  have hXnorm (z r : ℝ) (i : Fin 4) (hz : |z| ≤ delta)
      (hr : 7 / 8 < r) : ‖X (z / rho ^ 2) r i‖ = r := by
    have hb := abs_le.mp (hzsmall z hz)
    have ha : 0 ≤ (r ^ 2 + z / rho ^ 2) / 2 ∧
        0 ≤ (r ^ 2 - z / rho ^ 2) / 2 :=
      ⟨by nlinarith [sq_nonneg (r - 7 / 8)], by nlinarith [sq_nonneg (r - 7 / 8)]⟩
    have hx : (J2 (X (z / rho ^ 2) r i)).1 ^ 2 = (r ^ 2 + z / rho ^ 2) / 2 := by
      simp only [X, ContinuousLinearEquiv.apply_symm_apply, mul_pow, (hSigns i).1,
        one_mul, Real.sq_sqrt ha.1]
    have hy : (J2 (X (z / rho ^ 2) r i)).2 ^ 2 = (r ^ 2 - z / rho ^ 2) / 2 := by
      simp only [X, ContinuousLinearEquiv.apply_symm_apply, mul_pow, (hSigns i).2,
        one_mul, Real.sq_sqrt ha.2]
    nlinarith [hJ2 (X (z / rho ^ 2) r i), norm_nonneg (X (z / rho ^ 2) r i)]
  have hClassify (x : E2) (z : ℝ)
      (hx : rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = z) :
      ∃ i : Fin 4, x = X (z / rho ^ 2) ‖x‖ i := by
    have hQ : (J2 x).1 ^ 2 - (J2 x).2 ^ 2 = z / rho ^ 2 :=
      (eq_div_iff hrne).mpr (by nlinarith)
    have hfirst : Real.sqrt ((‖x‖ ^ 2 + z / rho ^ 2) / 2) = |(J2 x).1| := by
      rw [show (‖x‖ ^ 2 + z / rho ^ 2) / 2 = (J2 x).1 ^ 2 by linarith [hJ2 x]]
      exact Real.sqrt_sq_eq_abs _
    have hsecond : Real.sqrt ((‖x‖ ^ 2 - z / rho ^ 2) / 2) = |(J2 x).2| := by
      rw [show (‖x‖ ^ 2 - z / rho ^ 2) / 2 = (J2 x).2 ^ 2 by linarith [hJ2 x]]
      exact Real.sqrt_sq_eq_abs _
    have hcoord (i : Fin 4) :
        J2 (X (z / rho ^ 2) ‖x‖ i) = (sx i * |(J2 x).1|, sy i * |(J2 x).2|) := by
      simp only [X, ContinuousLinearEquiv.apply_symm_apply, hfirst, hsecond]
    rcases le_or_gt 0 (J2 x).1 with hx0 | hx0 <;>
      rcases le_or_gt 0 (J2 x).2 with hy0 | hy0
    · refine ⟨0, J2.injective ?_⟩
      rw [hcoord]
      apply Prod.ext <;> simp [sx, sy, abs_of_nonneg hx0, abs_of_nonneg hy0]
    · refine ⟨3, J2.injective ?_⟩
      rw [hcoord]
      apply Prod.ext <;> simp [sx, sy, abs_of_nonneg hx0, abs_of_neg hy0]
    · refine ⟨1, J2.injective ?_⟩
      rw [hcoord]
      apply Prod.ext <;> simp [sx, sy, abs_of_neg hx0, abs_of_nonneg hy0]
    · refine ⟨2, J2.injective ?_⟩
      rw [hcoord]
      apply Prod.ext <;> simp [sx, sy, abs_of_neg hx0, abs_of_neg hy0]
  have hOldQ (p : UnitTwoSphere) (hp : p ∈ N) (hpt : p ∈ ks.target)
      (hn : ‖ks.symm p‖ ≤ 2) :
      rho ^ 2 * ((J2 (ks.symm p)).1 ^ 2 - (J2 (ks.symm p)).2 ^ 2) = -delta := by
    have hh := (hCoordinates (ks.symm p)
      (by simpa only [mem_closedBall, dist_zero_right] using hn)).2
    rw [ks.right_inv hpt] at hh
    have hp' : H (j p) = c - delta := hp
    linarith
  have hOutPoint (t : ℝ) (p : UnitTwoSphere) (hp : p ∈ N) (hv : p ∉ Vs) :
      ∃ p' : UnitTwoSphere, j p' = Phi (sigma t * delta) (j p) ∧
        H (j p') = c - delta + sigma t * delta ∧ p' ∉ Vs := by
    have he : j p ∈ Elevel (-delta) := by
      refine ⟨⟨⟨p, rfl⟩, ?_⟩, ?_⟩
      · change H (j p) = c + -delta
        exact (show H (j p) = c - delta from hp).trans (by ring)
      · rintro ⟨p', hp', heq⟩
        exact hv ((hji heq) ▸ hp')
    have he' := (hExterior (sigma t * delta) (htime t)).subset ⟨j p, he, rfl⟩
    obtain ⟨p', hp'⟩ := he'.1.1
    change j p' = Phi (sigma t * delta) (j p) at hp'
    refine ⟨p', hp', ?_, ?_⟩
    · have hh : H (Phi (sigma t * delta) (j p)) = c + (-delta + sigma t * delta) := he'.1.2
      rw [hp']
      linarith
    · intro hv'
      exact he'.2 ⟨p', hv', hp'⟩
  have hOverlap (t : ℝ) (p : UnitTwoSphere) (hp : p ∈ N) (hpt : p ∈ ks.target)
      (hlo : 7 / 8 < ‖ks.symm p‖) (hhi : ‖ks.symm p‖ < 9 / 8) :
      kp (F t (ks.symm p)) = pi (Phi (sigma t * delta) (j p)) := by
    have hxQ := hOldQ p hp hpt (by linarith)
    obtain ⟨i, hxi⟩ := hClassify (ks.symm p) (-delta) hxQ
    have ha : ‖ks.symm p‖ - 1 ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) :=
      ⟨by linarith, by linarith⟩
    have har : 1 + (‖ks.symm p‖ - 1) = ‖ks.symm p‖ := by ring
    have hFi := hAngular t i (‖ks.symm p‖ - 1) ha
    rw [har, ← hxi] at hFi
    have hPi := hNative (sigma t * delta) (htime t) i (‖ks.symm p‖ - 1) ha
    rw [har, ← hxi, ks.right_inv hpt] at hPi
    have hproj := (hCoordinates (F t (ks.symm p)) (by
      simpa only [mem_closedBall, dist_zero_right, hFNorm] using
        (show ‖ks.symm p‖ ≤ 2 by linarith))).1
    calc
      kp (F t (ks.symm p)) = pi (j (ks (F t (ks.symm p)))) := hproj.symm
      _ = pi (j (ks (X ((-delta + sigma t * delta) / rho ^ 2) ‖ks.symm p‖ i))) :=
        congrArg (fun x => pi (j (ks x))) hFi
      _ = pi (Phi (sigma t * delta) (j p)) := congrArg pi hPi.symm
  have hAout (t : ℝ) (p : UnitTwoSphere) (hp : p ∉ Vs) :
      A t p = pi (Phi (sigma t * delta) (j p)) := by simp only [A, if_neg hp]
  have hAclosed (t : ℝ) (p : UnitTwoSphere) (hp : p ∈ N) (hc : p ∈ Cs) :
      A t p = kp (F t (ks.symm p)) := by
    by_cases hv : p ∈ Vs
    · simp only [A, if_pos hv]
    · have hn := hrim hc hv
      exact (hAout t p hv).trans
        (hOverlap t p hp (hsc hc).1 (by rw [hn]; norm_num) (by rw [hn]; norm_num)).symm
  have hOpen (t : ℝ) (p : UnitTwoSphere) (hp : p ∈ N) : A t p ∈ V ↔ p ∈ Vs := by
    constructor
    · intro hAV
      by_contra hv
      obtain ⟨p', heq, hh, hv'⟩ := hOutPoint t p hp hv
      apply hv'
      apply (hNoSheets (-delta + sigma t * delta) (hnew t) p' (by linarith)).1.mp
      rw [heq]
      rwa [hAout t p hv] at hAV
    · intro hv
      have hn := (hsv hv).2
      rw [show A t p = kp (F t (ks.symm p)) by simp only [A, if_pos hv]]
      exact ⟨F t (ks.symm p),
        by simpa only [mem_ball, dist_zero_right, hFNorm] using hn, rfl⟩
  have hClosed (t : ℝ) (p : UnitTwoSphere) (hp : p ∈ N) : A t p ∈ K ↔ p ∈ Cs := by
    constructor
    · intro hAK
      by_contra hc
      have hv : p ∉ Vs := fun h => hc (hVsCs h)
      obtain ⟨p', heq, hh, hv'⟩ := hOutPoint t p hp hv
      have hc' : p' ∈ Cs := by
        apply (hNoSheets (-delta + sigma t * delta) (hnew t) p' (by linarith)).2.mp
        rw [heq]
        rwa [hAout t p hv] at hAK
      have hpt := (hsc hc').1
      have hn := hrim hc' hv'
      have hQ : rho ^ 2 *
          ((J2 (ks.symm p')).1 ^ 2 - (J2 (ks.symm p')).2 ^ 2) = -delta + sigma t * delta := by
        have hcoord := (hCoordinates (ks.symm p') (by
          simpa only [mem_closedBall, dist_zero_right, hn] using (by norm_num : (1 : ℝ) ≤ 2))).2
        rw [ks.right_inv hpt] at hcoord
        linarith
      obtain ⟨i, hxi⟩ := hClassify (ks.symm p') (-delta + sigma t * delta) hQ
      rw [hn] at hxi
      have hport : ks (X ((-delta + sigma t * delta) / rho ^ 2) 1 i) = p' := by
        rw [← hxi, ks.right_inv hpt]
      have hOldNorm : ‖X (-delta / rho ^ 2) 1 i‖ = 1 :=
        hXnorm (-delta) 1 i
          (by simpa only [abs_neg, abs_of_pos hdelta] using le_refl delta) (by norm_num)
      have hOldCs : ks (X (-delta / rho ^ 2) 1 i) ∈ Cs :=
        ⟨X (-delta / rho ^ 2) 1 i,
          by simpa only [mem_closedBall, dist_zero_right, hOldNorm] using (le_refl (1 : ℝ)),
          rfl⟩
      have hNat := hNative (sigma t * delta) (htime t) i 0 (by constructor <;> norm_num)
      simp only [add_zero] at hNat
      rw [hport] at hNat
      have hOldEq : ks (X (-delta / rho ^ 2) 1 i) = p :=
        hji ((Phi (sigma t * delta)).injective (hNat.trans heq))
      exact hc (hOldEq ▸ hOldCs)
    · intro hc
      rw [hAclosed t p hp hc]
      exact ⟨F t (ks.symm p),
        by simpa only [mem_closedBall, dist_zero_right, hFNorm] using (hsc hc).2, rfl⟩
  have hInjective (t : ℝ) : InjOn (A t) N := by
    intro p hp q hq heq
    by_cases hpV : p ∈ Vs
    · have hqV : q ∈ Vs := (hOpen t q hq).mp (heq ▸ (hOpen t p hp).mpr hpV)
      have hpT := hsv hpV
      have hqT := hsv hqV
      have hpF : F t (ks.symm p) ∈ kp.source := hp2 (by
        rw [hFNorm]
        linarith [hpT.2])
      have hqF : F t (ks.symm q) ∈ kp.source := hp2 (by
        rw [hFNorm]
        linarith [hqT.2])
      simp only [A, if_pos hpV, if_pos hqV] at heq
      exact ks.symm.injOn hpT.1 hqT.1 ((F t).injective (kp.injOn hpF hqF heq))
    · have hqV : q ∉ Vs := by
        intro hv
        exact hpV ((hOpen t p hp).mp (heq.symm ▸ (hOpen t q hq).mpr hv))
      obtain ⟨p', hp', hHp, _⟩ := hOutPoint t p hp hpV
      obtain ⟨q', hq', hHq, _⟩ := hOutPoint t q hq hqV
      have hpi : pi (Phi (sigma t * delta) (j p)) = pi (Phi (sigma t * delta) (j q)) := by
        simpa only [A, if_neg hpV, if_neg hqV] using heq
      apply hji
      apply (Phi (sigma t * delta)).injective
      apply L.injective
      apply Prod.ext
      · exact hpi
      · change (heightPlaneCoordinates u (Phi (sigma t * delta) (j p))).2 =
          (heightPlaneCoordinates u (Phi (sigma t * delta) (j q))).2
        rw [heightPlaneCoordinates_snd, heightPlaneCoordinates_snd]
        change H (Phi (sigma t * delta) (j p)) = H (Phi (sigma t * delta) (j q))
        rw [← hp', ← hq']
        exact hHp.trans hHq.symm
  refine ⟨hInjective, fun t p hp =>
    ⟨hOpen t p hp, hClosed t p hp, hAclosed t p hp, hAout t p⟩, hOverlap, ?_, ?_⟩
  · intro t
    ext x
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hxV⟩
      have hpV : p ∉ Vs := fun hv => hxV ((hOpen t p hp).mpr hv)
      obtain ⟨p', hp', hh, _⟩ := hOutPoint t p hp hpV
      have hrec : L.symm (A t p, c - delta + sigma t * delta) =
          Phi (sigma t * delta) (j p) := by
        rw [hAout t p hpV]
        apply heightPlaneCoordinates_reconstruct u
        change H (Phi (sigma t * delta) (j p)) = _
        rw [← hp']
        exact hh
      refine ⟨?_, hxV⟩
      change L.symm (A t p, c - delta + sigma t * delta) ∈ S
      rw [hrec]
      exact ⟨p', hp'⟩
    · rintro ⟨hxS, hxV⟩
      obtain ⟨p, hp⟩ := hxS
      change j p = L.symm (x, c - delta + sigma t * delta) at hp
      have hpi : pi (j p) = x := by
        rw [hp]
        change (L (L.symm (x, c - delta + sigma t * delta))).1 = x
        simp only [ContinuousLinearEquiv.apply_symm_apply]
      have hheight : H (j p) = c - delta + sigma t * delta := by
        rw [hp]
        change ⟪(u : E3), L.symm (x, c - delta + sigma t * delta)⟫_ℝ = _
        rw [← heightPlaneCoordinates_snd u]
        change (L (L.symm (x, c - delta + sigma t * delta))).2 = _
        simp only [ContinuousLinearEquiv.apply_symm_apply]
      have hpV : p ∉ Vs := by
        intro hv
        apply hxV
        rw [← hpi]
        exact (hNoSheets (-delta + sigma t * delta) (hnew t) p (by linarith)).1.mpr hv
      have he : j p ∈ Elevel (-delta + sigma t * delta) := by
        refine ⟨⟨⟨p, rfl⟩, ?_⟩, ?_⟩
        · change H (j p) = c + (-delta + sigma t * delta)
          linarith
        · rintro ⟨p', hp', heq⟩
          exact hpV ((hji heq) ▸ hp')
      rw [← hExterior (sigma t * delta) (htime t)] at he
      obtain ⟨y, hy, hyeq⟩ := he
      obtain ⟨p0, hp0⟩ := hy.1.1
      have hp0N : p0 ∈ N := by
        have hh : H y = c + -delta := hy.1.2
        change H (j p0) = c - delta
        rw [hp0]
        linarith
      have hp0V : p0 ∉ Vs := fun hv => hy.2 ⟨p0, hv, hp0⟩
      refine ⟨⟨p0, hp0N, ?_⟩, hxV⟩
      change A t p0 = x
      rw [hAout t p0 hp0V, hp0, hyeq, hpi]
  · intro t
    ext x
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hxK⟩
      have hpC := (hClosed t p hp).mp hxK
      have hpt := hsc hpC
      have hq := hOldQ p hp hpt.1 (by linarith [hpt.2])
      exact ⟨F t (ks.symm p), ⟨ks.symm p, ⟨hpt.2, hq⟩, rfl⟩,
        (hAclosed t p hp hpC).symm⟩
    · rintro ⟨w, ⟨y, ⟨hy, hQ⟩, rfl⟩, rfl⟩
      have hys := hs2 (by linarith)
      have hpN : ks y ∈ N := by
        have hh := (hCoordinates y (by
          simpa only [mem_closedBall, dist_zero_right] using (show ‖y‖ ≤ 2 by linarith))).2
        change H (j (ks y)) = c - delta
        linarith
      have hpC : ks y ∈ Cs :=
        ⟨y, by simpa only [mem_closedBall, dist_zero_right] using hy, rfl⟩
      have hEq := hAclosed t (ks y) hpN hpC
      rw [ks.left_inv hys] at hEq
      exact ⟨⟨ks y, hpN, hEq⟩,
        ⟨F t y, by simpa only [mem_closedBall, dist_zero_right, hFNorm] using hy, rfl⟩⟩

end PoincareConjecture.M25.Topology3D
