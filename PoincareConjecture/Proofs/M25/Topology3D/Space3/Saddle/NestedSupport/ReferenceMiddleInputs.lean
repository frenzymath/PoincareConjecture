import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferencePlacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceSelectedWallField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MiddleExteriorCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix NNReal

namespace PoincareConjecture.M25.Topology3D

private theorem nested_reference_coordinate_scaling
    (rho rhoN Lambda : ℝ) (hrho : 0 < rho) (hrhoN : 0 < rhoN)
    (hLambda : 0 < Lambda) (hScale : Lambda * rhoN ^ 2 = rho ^ 2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (sigma sx sy : ℝ) (hsx : sx ^ 2 = 1) (hsy : sy ^ 2 = 1) :
    let xi : ℝ → ℝ → E2 := fun t r => J2.symm
      (sx * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
        sy * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
    (∀ (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ t : ℝ, |t / rho ^ 2| < 1 / 64 →
        ‖xi t r‖ = r ∧
        rho ^ 2 * ((J2 (xi t r)).1 ^ 2 - (J2 (xi t r)).2 ^ 2) = t) ∧
    ∀ t r : ℝ,
      (sigma * (sy * Real.sqrt ((rhoN ^ 2 * (1 + (r - 1)) ^ 2 -
          t / Lambda) / 2)),
        sigma * (sx * Real.sqrt ((rhoN ^ 2 * (1 + (r - 1)) ^ 2 +
          t / Lambda) / 2))) =
      (sigma * rhoN * (J2 (xi t r)).2,
        sigma * rhoN * (J2 (xi t r)).1) := by
  intro xi
  constructor
  · intro r hr t ht
    have hp : 0 ≤ (r ^ 2 + t / rho ^ 2) / 2 := by
      nlinarith only [hr.1, (abs_lt.mp ht).1, sq_nonneg (r - 15 / 16)]
    have hm : 0 ≤ (r ^ 2 - t / rho ^ 2) / 2 := by
      nlinarith only [hr.1, (abs_lt.mp ht).2, sq_nonneg (r - 15 / 16)]
    have hx0 : (J2 (xi t r)).1 ^ 2 = (r ^ 2 + t / rho ^ 2) / 2 := by
      simp only [xi, J2.apply_symm_apply, mul_pow, hsx, one_mul, Real.sq_sqrt hp]
    have hx1 : (J2 (xi t r)).2 ^ 2 = (r ^ 2 - t / rho ^ 2) / 2 := by
      simp only [xi, J2.apply_symm_apply, mul_pow, hsy, one_mul, Real.sq_sqrt hm]
    have hn : ‖xi t r‖ ^ 2 = r ^ 2 := by rw [← hJ2, hx0, hx1]; ring
    refine ⟨by nlinarith only [hn, norm_nonneg (xi t r), hr.1], ?_⟩
    rw [hx0, hx1]
    field_simp [hrho.ne']
    ring
  · intro t r
    have htime : t / Lambda = rhoN ^ 2 * (t / rho ^ 2) := by
      rw [← hScale]
      field_simp [hLambda.ne', hrhoN.ne']
    have hsqrt (v : ℝ) : Real.sqrt (rhoN ^ 2 * v) = rhoN * Real.sqrt v := by
      rw [Real.sqrt_mul (sq_nonneg rhoN), Real.sqrt_sq hrhoN.le]
    dsimp only [xi]
    rw [J2.apply_symm_apply, htime]
    have hr1 : 1 + (r - 1) = r := by ring
    rw [hr1]
    have hm : (rhoN ^ 2 * r ^ 2 - rhoN ^ 2 * (t / rho ^ 2)) / 2 =
        rhoN ^ 2 * ((r ^ 2 - t / rho ^ 2) / 2) := by ring
    have hp : (rhoN ^ 2 * r ^ 2 + rhoN ^ 2 * (t / rho ^ 2)) / 2 =
        rhoN ^ 2 * ((r ^ 2 + t / rho ^ 2) / 2) := by ring
    rw [hm, hp, hsqrt, hsqrt]
    apply Prod.ext <;> dsimp only <;> ring

theorem exists_saddle_nested_reference_middle_inputs
    (ws wm d sigma : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hsigma : sigma = 1 ∨ sigma = -1)
    (m : OpenPartialHomeomorph E2 (ℝ × ℝ))
    (hm_point : (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2) ∈ m.source)
    (hm_source : m.source ⊆ ball (0 : E2) 1)
    (hm_zero : m (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2) = 0)
    (hm : ContDiffOn ℝ ∞ m m.source)
    (hmi : ContDiffOn ℝ ∞ m.symm m.target)
    (hm_height : ∀ v ∈ m.source,
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 =
        1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 -
          (m v).1 ^ 2 + (m v).2 ^ 2)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (c rho : ℝ) (hrho : 0 < rho) :
    let h8 := exists_nestedReference_buffered_morse_chart
      ws hwslo hwshi m hm_point hm_source hm_zero hm hmi hm_height
    let R : ℝ := Classical.choose h8
    let h8R := Classical.choose_spec h8
    let _bN : ℝ := Classical.choose h8R
    let h8b := Classical.choose_spec h8R
    let e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ) :=
      Classical.choose h8b
    let h8e := Classical.choose_spec h8b
    let Pnative : OpenPartialHomeomorph (ℝ × ℝ) E2 := Classical.choose h8e
    let rhoN : ℝ := R / 2
    let Lambda : ℝ := rho ^ 2 / rhoN ^ 2
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let mu : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    let L := heightPlaneCoordinates u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
    let S0 : Set E3 := (nestedReferenceBallChart d).boundary
    let sN : E2 → ℝ × ℝ := fun x =>
      (sigma * rhoN * (J2 x).2, sigma * rhoN * (J2 x).1)
    let Q : E2 → ℝ := fun x => (J2 x).1 ^ 2 - (J2 x).2 ^ 2
    let Do : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rhoN ^ 2}
    let Dc : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rhoN ^ 2}
    ∃ (kref : OpenPartialHomeomorph E2 E2)
      (gNative g : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (A : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞),
      let Sp : Set E3 := A '' S0
      0 < rhoN ∧ 0 < Lambda ∧ Lambda * rhoN ^ 2 = rho ^ 2 ∧
      kref.source = ball (0 : E2) 4 ∧ kref.target = Pnative.target ∧
      (∀ x : E2, kref x = Pnative (sN x)) ∧
      (∀ v : E2, kref.symm v = J2.symm
        (sigma / rhoN * (Pnative.symm v).2,
          sigma / rhoN * (Pnative.symm v).1)) ∧
      ContDiffOn ℝ ∞ kref kref.source ∧
      ContDiffOn ℝ ∞ kref.symm kref.target ∧
      EqOn gNative kref (closedBall (0 : E2) 2) ∧
      EqOn gNative.symm kref.symm (kref '' closedBall (0 : E2) 2) ∧
      EqOn g kappa (closedBall (0 : E2) 2) ∧
      EqOn g.symm kappa.symm (kappa '' closedBall (0 : E2) 2) ∧
      (∀ y : E3, A y = L.symm
        (g (gNative.symm (heightCoordinates y).1),
          c + Lambda * (H0 y - k - d))) ∧
      (∀ y : E3, A.symm y = heightCoordinates.symm
        (gNative (g.symm (L y).1), k + d + (H y - c) / Lambda)) ∧
      (∀ y : E3, H (A y) = c + Lambda * (H0 y - k - d)) ∧
      (∀ y : E3, H0 (A.symm y) = k + d + (H y - c) / Lambda) ∧
      IsCompact Sp ∧ Sp = range (fun q : UnitTwoSphere => A (j q)) ∧
      (∀ x ∈ closedBall (0 : E2) 2,
        sN x ∈ Pnative.source ∧ sN x ∈ e.target ∧
        e.symm (sN x) ∈ e.source ∧
        A (j (e.symm (sN x))) = L.symm (g x, c + rho ^ 2 * Q x)) ∧
      (∀ (t : ℝ), |t| < rho ^ 2 → ∀ x ∈ closedBall (0 : E2) 2,
        (L.symm (g x, c + t) ∈ Sp ↔ t = rho ^ 2 * Q x)) ∧
      (∀ (t : ℝ), |t| < rho ^ 2 → ∀ p : UnitTwoSphere,
        H (A (j p)) = c + t →
        ((L (A (j p))).1 ∈ g '' ball (0 : E2) 1 ↔ p ∈ Do) ∧
        ((L (A (j p))).1 ∈ g '' closedBall (0 : E2) 1 ↔ p ∈ Dc)) ∧
      ∀ (deltaN : ℝ) (hdeltaN : 0 < deltaN)
        (hsmallN : deltaN ≤ rhoN ^ 2 / 128)
        (hgapLo : 4 * deltaN < k - 17 / 16)
        (hgapHi : 4 * deltaN < mu - k),
      let delta : ℝ := Lambda * deltaN
      let hField := NestedReferenceLower.exists_reference_selected_wall_field
        ws wm d sigma hwslo hwshi hwsroot hwmlo hwmhi hwmroot hsigma
        m hm_point hm_source hm_zero hm hmi hm_height
        deltaN hdeltaN hsmallN hgapLo hgapHi
      let hFieldF := Classical.choose_spec hField
      let XN : E3 → E3 := Classical.choose hFieldF
      let hFieldX := Classical.choose_spec hFieldF
      let hXN : ContDiff ℝ ∞ XN := hFieldX.2.2.1
      let hcXN : HasCompactSupport XN := hFieldX.2.2.2.1
      ∀ (K B : ℝ≥0) (hK : LipschitzWith K XN) (hB : ∀ y : E3, ‖XN y‖ ≤ B),
      let TN : ℝ → ℝ →
          Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
        fun s t => boundedFlowDiffeomorph XN hK hB hXN hcXN (t - s)
      let EN : ℝ → Set E3 := fun t =>
        (S0 ∩ {y : E3 | H0 y = k + d + t}) \ (j '' Do)
      (∀ s t : ℝ, TN s t '' S0 = S0 ∧ (TN s t).symm '' S0 = S0) →
      (∀ s t : ℝ, |s| ≤ 2 * deltaN → |t| ≤ 2 * deltaN →
        TN s t '' EN s = EN t ∧ (TN s t).symm '' EN t = EN s) →
      let X : E3 → E3 := fun y =>
        (1 / Lambda) • fderiv ℝ A (A.symm y) (XN (A.symm y))
      let T : ℝ → ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
        fun s t => (A.symm.trans (TN (s / Lambda) (t / Lambda))).trans A
      let C : Set E3 := A '' tsupport XN
      let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
      let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
      let xi : Fin 4 → ℝ → ℝ → E2 := fun i t r => J2.symm
        (sx i * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
          sy i * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
      let Xi : Fin 4 → ℝ → ℝ → E3 := fun i t r =>
        L.symm (g (xi i t r), c + t)
      let qN : Fin 4 → ℝ → ℝ → UnitTwoSphere := fun i t a => e.symm
        (sigma * (sy i * Real.sqrt ((rhoN ^ 2 * (1 + a) ^ 2 - t) / 2)),
          sigma * (sx i * Real.sqrt ((rhoN ^ 2 * (1 + a) ^ 2 + t) / 2)))
      let E : ℝ → Set E2 := fun t =>
        {x | L.symm (g x, c + t) ∈ Sp ∧ 1 ≤ ‖x‖}
      let Ext : ℝ → Set E3 := fun t =>
        L.symm '' ((g '' E t) ×ˢ ({c + t} : Set ℝ))
      0 < delta ∧ delta ≤ rho ^ 2 / 128 ∧
      4 * delta < Lambda * (k - 17 / 16) ∧
      4 * delta < Lambda * (mu - k) ∧
      ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ IsCompact C ∧
      (∀ (t : ℝ), |t| < 2 * delta → ∀ x : E2, ‖x‖ < 2 →
        (L.symm (g x, c + t) ∈ Sp ↔ t = rho ^ 2 * Q x)) ∧
      (∀ (i : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ t : ℝ, |t| < 2 * delta →
          A (j (qN i (t / Lambda) (r - 1))) = Xi i t r) ∧
      (∀ (i : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun s : ℝ => Xi i s r) (X (Xi i t r)) t) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 => T p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 => (T p.1.1 p.1.2).symm p.2) ∧
      (∀ s t : ℝ, ∀ y : E3,
        T s t y = A (boundedFlow XN hK hB (A.symm y) ((t - s) / Lambda)) ∧
        (T s t).symm y =
          A (boundedFlow XN hK hB (A.symm y) ((s - t) / Lambda))) ∧
      (∀ s : ℝ, ∀ y : E3, T s s y = y) ∧
      (∀ s t : ℝ, ∀ y : E3,
        HasDerivAt (fun a : ℝ => T s a y) (X (T s t y)) t) ∧
      (∀ s t : ℝ, T s t '' Sp = Sp ∧ (T s t).symm '' Sp = Sp) ∧
      (∀ s t : ℝ,
        tsupport (fun y : E3 => T s t y - y) ⊆ C ∧
        tsupport (fun y : E3 => (T s t).symm y - y) ⊆ C) ∧
      (∀ t : ℝ, |t| ≤ 2 * delta → Ext t = A '' EN (t / Lambda)) ∧
      ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
        T s t '' Ext s = Ext t ∧ (T s t).symm '' Ext t = Ext s := by
  classical
  intro h8 R h8R bN h8b e h8e Pnative rhoN Lambda k mu L H H0 j S0 sN Q Do Dc
  clear_value h8 h8R h8b h8e
  have hPlacement := NestedReferenceLower.exists_reference_placement ws hwslo hwshi
    m hm_point hm_source hm_zero hm hmi hm_height
    sigma hsigma kappa hkappaSource hkappa hkappaInv J2 hJ2 u c rho d hrho
  obtain ⟨kref, gNative, g, A, hR, _hb, _hRb, hrhoN, hLambda, hScale,
    hkSource, hkTarget, hkForm, hkInverse, hkSmooth, hkInvSmooth, hNorm,
    hgNative, hgNativeInv, hg, hgInv, _hgImage, hA, hAi, hAH, hAiH,
    _hAsm, _hAism, _hFsm, _hFism, _hBchart, _hBsource, _hBtarget,
    _hBinside, _hBclosed, hBboundary, hBrange, _hBregions, _hstar,
    hPoint, _hLocalInverse, hLocal⟩ := hPlacement
  change 0 < rhoN at hrhoN
  change 0 < Lambda at hLambda
  change Lambda * rhoN ^ 2 = rho ^ 2 at hScale
  change ∀ x : E2,
    (sN x).1 ^ 2 + (sN x).2 ^ 2 = rhoN ^ 2 * ‖x‖ ^ 2 ∧
      -(sN x).1 ^ 2 + (sN x).2 ^ 2 = rhoN ^ 2 * Q x at hNorm
  clear hR _hb _hRb _hgImage _hAsm _hAism _hFsm _hFism _hBchart
    _hBsource _hBtarget _hBinside _hBclosed _hBregions _hstar _hLocalInverse
  let Sp : Set E3 := A '' S0
  have hHeight (y : E3) : H (A y) = c + Lambda * (H0 y - k - d) := hAH y
  have hInverse (y : E3) : A.symm y = heightCoordinates.symm
      (gNative (g.symm (L y).1), k + d + (H y - c) / Lambda) := by
    simpa only [H, L, heightPlaneCoordinates_snd,
      InnerProductSpace.toDual_apply_apply] using hAi y
  have hRange : Sp = range (fun q : UnitTwoSphere => A (j q)) :=
    hBboundary.symm.trans hBrange
  have hCompact : IsCompact Sp := by
    rw [hRange]
    exact isCompact_range (A.continuous.comp
      ((nestedReferenceDiffeomorph d).continuous.comp continuous_subtype_val))
  have hj : Injective j := fun p q h => Subtype.ext
    ((nestedReferenceDiffeomorph d).injective h)
  have hPoint' (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      sN x ∈ Pnative.source ∧ sN x ∈ e.target ∧
      e.symm (sN x) ∈ e.source ∧
      A (j (e.symm (sN x))) = L.symm (g x, c + rho ^ 2 * Q x) := by
    obtain ⟨_, hp, he, hes, heq⟩ := hPoint x hx
    refine ⟨hp, he, hes, ?_⟩
    change A (j (e.symm (sN x))) = L.symm (kappa x, c + rho ^ 2 * Q x) at heq
    rwa [← hg hx] at heq
  have hGraph (t : ℝ) (ht : |t| < rho ^ 2)
      (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      L.symm (g x, c + t) ∈ Sp ↔ t = rho ^ 2 * Q x := by
    have hh := (hLocal x hx t ht).2.2.2.2.2.1
    rw [hBboundary] at hh
    simpa only [hg hx] using hh
  have hsigmaSq : sigma ^ 2 = 1 := by
    rcases hsigma with h | h <;> norm_num [h]
  let invS : (ℝ × ℝ) → E2 := fun s =>
    J2.symm (sigma / rhoN * s.2, sigma / rhoN * s.1)
  have hInvS (s : ℝ × ℝ) : sN (invS s) = s := by
    dsimp only [sN, invS]
    rw [J2.apply_symm_apply]
    apply Prod.ext <;> dsimp only
    · calc
        sigma * rhoN * (sigma / rhoN * s.1) = sigma ^ 2 * s.1 := by
          field_simp [hrhoN.ne']
        _ = s.1 := by rw [hsigmaSq, one_mul]
    · calc
        sigma * rhoN * (sigma / rhoN * s.2) = sigma ^ 2 * s.2 := by
          field_simp [hrhoN.ne']
        _ = s.2 := by rw [hsigmaSq, one_mul]
  have hDiscImages :
      (fun x : E2 => e.symm (sN x)) '' ball (0 : E2) 1 = Do ∧
      (fun x : E2 => e.symm (sN x)) '' closedBall (0 : E2) 1 = Dc := by
    have hrad (s : ℝ × ℝ) :
        rhoN ^ 2 * ‖invS s‖ ^ 2 = s.1 ^ 2 + s.2 ^ 2 := by
      rw [← (hNorm (invS s)).1, hInvS]
    have hp := sq_pos_of_pos hrhoN
    constructor
    · ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨sN x, ?_, rfl⟩
        change (sN x).1 ^ 2 + (sN x).2 ^ 2 < rhoN ^ 2
        rw [(hNorm x).1]
        have hn := mem_ball_zero_iff.mp hx
        have hn2 : ‖x‖ ^ 2 < 1 := by nlinarith only [hn, norm_nonneg x]
        simpa only [mul_one] using mul_lt_mul_of_pos_left hn2 hp
      · rintro ⟨s, hs, rfl⟩
        refine ⟨invS s, mem_ball_zero_iff.mpr ?_, congrArg e.symm (hInvS s)⟩
        change s.1 ^ 2 + s.2 ^ 2 < rhoN ^ 2 at hs
        have hh : rhoN ^ 2 * ‖invS s‖ ^ 2 < rhoN ^ 2 * 1 := by
          simpa only [mul_one, hrad] using hs
        have hn2 := lt_of_mul_lt_mul_left hh hp.le
        nlinarith only [hn2, norm_nonneg (invS s)]
    · ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨sN x, ?_, rfl⟩
        change (sN x).1 ^ 2 + (sN x).2 ^ 2 ≤ rhoN ^ 2
        rw [(hNorm x).1]
        have hn := mem_closedBall_zero_iff.mp hx
        have hn2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith only [hn, norm_nonneg x]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hn2 hp.le
      · rintro ⟨s, hs, rfl⟩
        refine ⟨invS s, mem_closedBall_zero_iff.mpr ?_, congrArg e.symm (hInvS s)⟩
        change s.1 ^ 2 + s.2 ^ 2 ≤ rhoN ^ 2 at hs
        have hh : rhoN ^ 2 * ‖invS s‖ ^ 2 ≤ rhoN ^ 2 * 1 := by
          simpa only [mul_one, hrad] using hs
        have hn2 := le_of_mul_le_mul_left hh hp
        nlinarith only [hn2, norm_nonneg (invS s)]
  have hNoSheets (t : ℝ) (ht : |t| < rho ^ 2) (p : UnitTwoSphere)
      (hh : H (A (j p)) = c + t) :
      ((L (A (j p))).1 ∈ g '' ball (0 : E2) 1 ↔ p ∈ Do) ∧
      ((L (A (j p))).1 ∈ g '' closedBall (0 : E2) 1 ↔ p ∈ Dc) := by
    have hlocal (B : Set E2) (hB : B ⊆ closedBall (0 : E2) 1) :
        (L (A (j p))).1 ∈ g '' B ↔ p ∈
          (fun x : E2 => e.symm (sN x)) '' B := by
      constructor
      · rintro ⟨x, hx, hxp⟩
        have hx2 : x ∈ closedBall (0 : E2) 2 :=
          (closedBall_subset_closedBall (by norm_num)) (hB hx)
        have heq : A (j p) = L.symm (g x, c + t) := by
          apply L.injective
          rw [L.apply_symm_apply]
          apply Prod.ext hxp.symm
          exact (heightPlaneCoordinates_snd u _).trans hh
        have hm : L.symm (g x, c + t) ∈ Sp := by
          rw [← heq, hRange]
          exact mem_range_self p
        have hq := (hGraph t ht x hx2).mp hm
        have he := (hPoint' x hx2).2.2.2
        rw [← hq] at he
        exact ⟨x, hx, (hj (A.injective (heq.trans he.symm))).symm⟩
      · rintro ⟨x, hx, rfl⟩
        have hx2 : x ∈ closedBall (0 : E2) 2 :=
          (closedBall_subset_closedBall (by norm_num)) (hB hx)
        refine ⟨x, hx, ?_⟩
        rw [(hPoint' x hx2).2.2.2, L.apply_symm_apply]
    exact ⟨(hlocal _ ball_subset_closedBall).trans (Set.ext_iff.mp hDiscImages.1 p),
      (hlocal _ Subset.rfl).trans (Set.ext_iff.mp hDiscImages.2 p)⟩
  refine ⟨kref, gNative, g, A, hrhoN, hLambda, hScale, hkSource, hkTarget,
    hkForm, hkInverse, hkSmooth, hkInvSmooth, hgNative, hgNativeInv, hg, hgInv,
    hA, hInverse, hHeight, hAiH, hCompact, hRange, hPoint', hGraph, hNoSheets, ?_⟩
  intro deltaN hdeltaN hsmallN hgapLo hgapHi delta hField hFieldF XN hFieldX hXN hcXN
    K B hK hB TN EN hNativeSurface hNativeExterior X T C sx sy xi Xi qN E Ext
  clear_value hField hFieldF hFieldX hXN hcXN
  have hNativeDeriv := hFieldX.2.2.2.2.2.2.2.2.2.2
  have hnd (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8)
      (t : ℝ) (ht : |t| ≤ 2 * deltaN) :
      HasDerivAt (fun v : ℝ => j (qN i v a)) (XN (j (qN i t a))) t := by
    simpa only [qN, j, sx, sy, add_zero, one_smul] using hNativeDeriv i a ha t ht
  clear hNativeDeriv
  have hdelta : 0 < delta := mul_pos hLambda hdeltaN
  have hsmall : delta ≤ rho ^ 2 / 128 := by
    have hh := mul_le_mul_of_nonneg_left hsmallN hLambda.le
    change Lambda * deltaN ≤ rho ^ 2 / 128
    nlinarith only [hh, hScale]
  have hLo : 4 * delta < Lambda * (k - 17 / 16) := by
    have hh := mul_lt_mul_of_pos_left hgapLo hLambda
    change 4 * (Lambda * deltaN) < _
    nlinarith only [hh]
  have hHi : 4 * delta < Lambda * (mu - k) := by
    have hh := mul_lt_mul_of_pos_left hgapHi hLambda
    change 4 * (Lambda * deltaN) < _
    nlinarith only [hh]
  have htime (t : ℝ) (ht : |t| ≤ 2 * delta) : |t / Lambda| ≤ 2 * deltaN := by
    rw [abs_div, abs_of_pos hLambda, div_le_iff₀ hLambda]
    change |t| ≤ 2 * (Lambda * deltaN) at ht
    nlinarith only [ht]
  have hsmallTime (t : ℝ) (ht : |t| ≤ 2 * delta) : |t| < rho ^ 2 := by
    nlinarith only [ht, hsmall, sq_pos_of_pos hrho]
  have hX : ContDiff ℝ ∞ X := (contDiff_const (c := (1 / Lambda : ℝ))).smul
    (((A.contDiff.fderiv_right (by simp)).comp A.symm.contDiff).clm_apply
      (hXN.comp A.symm.contDiff))
  have hC : IsCompact C := hcXN.isCompact.image A.continuous
  have hzero (y : E3) (hy : y ∉ C) : XN (A.symm y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hy ⟨A.symm y, hh, A.apply_symm_apply y⟩
  have hXsupport : tsupport X ⊆ C := by
    apply closure_minimal ?_ hC.isClosed
    intro y hy
    by_contra hnot
    apply hy
    simp only [X, hzero y hnot, map_zero, smul_zero]
  have hcX : HasCompactSupport X := hC.of_isClosed_subset (isClosed_tsupport X) hXsupport
  have hGraph' (t : ℝ) (ht : |t| < 2 * delta) (x : E2) (hx : ‖x‖ < 2) :
      L.symm (g x, c + t) ∈ Sp ↔ t = rho ^ 2 * Q x :=
    hGraph t (hsmallTime t ht.le) x (mem_closedBall_zero_iff.mpr hx.le)
  have hsign (i : Fin 4) : (sx i) ^ 2 = 1 ∧ (sy i) ^ 2 = 1 := by
    fin_cases i <;> norm_num [sx, sy]
  have hcoords (i : Fin 4) := nested_reference_coordinate_scaling
    rho rhoN Lambda hrho hrhoN hLambda hScale J2 hJ2 sigma
    (sx i) (sy i) (hsign i).1 (hsign i).2
  have hxi (i : Fin 4) (r : ℝ) (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) :
      ‖xi i t r‖ = r ∧ rho ^ 2 * Q (xi i t r) = t := by
    have hquot : |t / rho ^ 2| < 1 / 64 := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hrho), div_lt_iff₀ (sq_pos_of_pos hrho)]
      linarith only [ht, hsmall]
    exact (hcoords i).1 r hr t hquot
  have hNativePoint (i : Fin 4) (t r : ℝ) :
      qN i (t / Lambda) (r - 1) = e.symm (sN (xi i t r)) := by
    exact congrArg e.symm ((hcoords i).2 t r)
  have hPlacedPoint (i : Fin 4) (r : ℝ)
      (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16)) (t : ℝ) (ht : |t| < 2 * delta) :
      A (j (qN i (t / Lambda) (r - 1))) = Xi i t r := by
    rw [hNativePoint]
    have hx := hxi i r hr t ht
    have hx2 : xi i t r ∈ closedBall (0 : E2) 2 :=
      mem_closedBall_zero_iff.mpr (by rw [hx.1]; linarith only [hr.2])
    simpa only [hx.2] using (hPoint' (xi i t r) hx2).2.2.2
  have hpost (f : E3 → E3) (hf : ContDiff ℝ ∞ f)
      (q : ℝ → E3) (v : E3) (t : ℝ) (hq : HasDerivAt q v t) :
      HasDerivAt (fun a : ℝ => f (q a)) (fderiv ℝ f (q t) v) t :=
    (hf.differentiable (by simp) (q t)).hasFDerivAt.comp_hasDerivAt t hq
  have hTrack (i : Fin 4) (r : ℝ)
      (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16)) (t : ℝ) (ht : |t| < 2 * delta) :
      HasDerivAt (fun s : ℝ => Xi i s r) (X (Xi i t r)) t := by
    have ha : |r - 1| < 1 / 8 := abs_lt.mpr
      ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
    have hn := (hnd i (r - 1) ha (t / Lambda) (htime t ht.le)).scomp t
      ((hasDerivAt_id t).div_const Lambda)
    have hd := hpost A A.contDiff _ _ t hn
    have hinv : A.symm (Xi i t r) = j (qN i (t / Lambda) (r - 1)) := by
      rw [← hPlacedPoint i r hr t ht, A.symm_apply_apply]
    have hd' : HasDerivAt
        (fun s : ℝ => A (j (qN i (s / Lambda) (r - 1)))) (X (Xi i t r)) t := by
      simpa only [Function.comp_def, id_eq, X, hinv, map_smul] using hd
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2] with s hs
    exact (hPlacedPoint i r hr s (abs_lt.mpr hs)).symm
  have hForm (s t : ℝ) (y : E3) :
      T s t y = A (boundedFlow XN hK hB (A.symm y) ((t - s) / Lambda)) ∧
      (T s t).symm y = A (boundedFlow XN hK hB (A.symm y) ((s - t) / Lambda)) := by
    constructor
    · change A (boundedFlow XN hK hB (A.symm y) (t / Lambda - s / Lambda)) = _
      congr 2
      ring
    · change A (boundedFlow XN hK hB (A.symm y) (-(t / Lambda - s / Lambda))) = _
      congr 2
      ring
  have hTsm : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 => T p.1.1 p.1.2 p.2) := by
    have heq : (fun p : (ℝ × ℝ) × E3 => T p.1.1 p.1.2 p.2) =
        (fun p : (ℝ × ℝ) × E3 =>
          A (boundedFlow XN hK hB (A.symm p.2) ((p.1.2 - p.1.1) / Lambda))) :=
      funext fun p => (hForm p.1.1 p.1.2 p.2).1
    rw [heq]
    exact A.contDiff.comp ((boundedFlow_contDiff XN hK hB hXN hcXN).comp
      ((A.symm.contDiff.comp contDiff_snd).prodMk
        (((contDiff_snd.comp contDiff_fst).sub
          (contDiff_fst.comp contDiff_fst)).div_const Lambda)))
  have hTism : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 => (T p.1.1 p.1.2).symm p.2) := by
    have heq : (fun p : (ℝ × ℝ) × E3 => (T p.1.1 p.1.2).symm p.2) =
        (fun p : (ℝ × ℝ) × E3 =>
          A (boundedFlow XN hK hB (A.symm p.2) ((p.1.1 - p.1.2) / Lambda))) :=
      funext fun p => (hForm p.1.1 p.1.2 p.2).2
    rw [heq]
    exact A.contDiff.comp ((boundedFlow_contDiff XN hK hB hXN hcXN).comp
      ((A.symm.contDiff.comp contDiff_snd).prodMk
        (((contDiff_fst.comp contDiff_fst).sub
          (contDiff_snd.comp contDiff_fst)).div_const Lambda)))
  have hTself (s : ℝ) (y : E3) : T s s y = y := by
    rw [(hForm s s y).1, sub_self, zero_div, boundedFlow_zero, A.apply_symm_apply]
  have hTder (s t : ℝ) (y : E3) :
      HasDerivAt (fun a : ℝ => T s a y) (X (T s t y)) t := by
    have hb := (boundedFlow_hasDerivAt XN hK hB (A.symm y) ((t - s) / Lambda)).scomp t
      (((hasDerivAt_id t).sub_const s).div_const Lambda)
    have hd := hpost A A.contDiff _ _ t hb
    have hd' : HasDerivAt
        (fun a : ℝ => A (boundedFlow XN hK hB (A.symm y) ((a - s) / Lambda)))
        (X (T s t y)) t := by
      simpa only [X, (hForm s t y).1, A.symm_apply_apply, map_smul,
        Function.comp_def, id_eq] using hd
    exact hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun a => (hForm s a y).1))
  have hImages (s t : ℝ) (Z : Set E3) :
      T s t '' (A '' Z) = A '' (TN (s / Lambda) (t / Lambda) '' Z) ∧
      (T s t).symm '' (A '' Z) = A '' ((TN (s / Lambda) (t / Lambda)).symm '' Z) := by
    constructor
    · rw [← image_comp, ← image_comp]
      congr 1
      funext y
      change A (TN (s / Lambda) (t / Lambda) (A.symm (A y))) =
        A (TN (s / Lambda) (t / Lambda) y)
      rw [A.symm_apply_apply]
    · rw [← image_comp, ← image_comp]
      congr 1
      funext y
      change A ((TN (s / Lambda) (t / Lambda)).symm (A.symm (A y))) =
        A ((TN (s / Lambda) (t / Lambda)).symm y)
      rw [A.symm_apply_apply]
  have hSurface (s t : ℝ) : T s t '' Sp = Sp ∧ (T s t).symm '' Sp = Sp := by
    constructor
    · rw [(hImages s t S0).1, (hNativeSurface (s / Lambda) (t / Lambda)).1]
    · rw [(hImages s t S0).2, (hNativeSurface (s / Lambda) (t / Lambda)).2]
  have hFix (s t : ℝ) (y : E3) (hy : y ∉ C) :
      T s t y = y ∧ (T s t).symm y = y := by
    rw [(hForm s t y).1, (hForm s t y).2,
      boundedFlow_eq_self XN hK hB (A.symm y) (hzero y hy),
      boundedFlow_eq_self XN hK hB (A.symm y) (hzero y hy), A.apply_symm_apply]
    exact ⟨rfl, rfl⟩
  have hSupport (s t : ℝ) :
      tsupport (fun y : E3 => T s t y - y) ⊆ C ∧
      tsupport (fun y : E3 => (T s t).symm y - y) ⊆ C := by
    constructor
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hh
      exact hy (sub_eq_zero.mpr (hFix s t y hh).1)
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hh
      exact hy (sub_eq_zero.mpr (hFix s t y hh).2)
  have hHeightIff (y : E3) (t : ℝ) :
      H (A y) = c + t ↔ H0 y = k + d + t / Lambda := by
    rw [hHeight]
    constructor
    · intro hh
      apply (mul_left_cancel₀ hLambda.ne')
      rw [mul_add, mul_div_cancel₀ t hLambda.ne']
      nlinarith only [hh]
    · intro hh
      rw [hh]
      have hc : k + d + t / Lambda - k - d = t / Lambda := by ring
      rw [hc, mul_div_cancel₀ t hLambda.ne']
  have hExterior (t : ℝ) (ht : |t| ≤ 2 * delta) : Ext t = A '' EN (t / Lambda) := by
    have he := saddle_middle_exterior_source_disc u c t g
      (fun p : UnitTwoSphere => A (j p)) Do (A.injective.comp hj)
      (fun p hp => by
        simpa only [horizontalBandProjection_apply] using
          (hNoSheets t (hsmallTime t ht) p hp).1)
    rw [← hRange] at he
    change Ext t = (Sp ∩ {y : E3 | H y = c + t}) \
      ((fun p : UnitTwoSphere => A (j p)) '' Do) at he
    rw [he]
    ext y
    constructor
    · rintro ⟨⟨⟨w, hw, rfl⟩, hh⟩, hnot⟩
      refine ⟨w, ⟨⟨hw, (hHeightIff w t).mp hh⟩, ?_⟩, rfl⟩
      rintro ⟨p, hp, hpw⟩
      exact hnot ⟨p, hp, congrArg A hpw⟩
    · rintro ⟨w, ⟨⟨hw, hh⟩, hnot⟩, rfl⟩
      refine ⟨⟨⟨w, hw, rfl⟩, (hHeightIff w t).mpr hh⟩, ?_⟩
      rintro ⟨p, hp, hpw⟩
      exact hnot ⟨p, hp, A.injective hpw⟩
  refine ⟨hdelta, hsmall, hLo, hHi, hX, hcX, hC, hGraph', hPlacedPoint, hTrack,
    hTsm, hTism, hForm, hTself, hTder, hSurface, hSupport, hExterior, ?_⟩
  intro s t hs ht
  rw [hExterior s hs, hExterior t ht]
  exact ⟨(hImages s t _).1.trans
      (congrArg (fun Z : Set E3 => A '' Z)
        (hNativeExterior (s / Lambda) (t / Lambda) (htime s hs) (htime t ht)).1),
    (hImages s t _).2.trans
      (congrArg (fun Z : Set E3 => A '' Z)
        (hNativeExterior (s / Lambda) (t / Lambda) (htime s hs) (htime t ht)).2)⟩

end PoincareConjecture.M25.Topology3D
