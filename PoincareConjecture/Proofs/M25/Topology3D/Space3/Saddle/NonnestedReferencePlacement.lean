import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarBallChartExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceRadialCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_saddle_nonnested_reference_placement
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (c r : ℝ) (hr : 0 < r)
    (rho : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 16)
    (hdEq : ∀ q : ℝ, 0 ≤ q → q ≤ rho / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2) :
    let L := heightPlaneCoordinates u
    let R0 := nonnestedReferenceBallChart 0 d hd
    ∃ (a : ℝ)
      (G : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (A : Diffeomorph 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, E3)
        ((ℝ × ℝ) × ℝ) E3 ∞),
    let F := (nonnestedReferenceDiffeomorph 0 d hd).trans A
    let B := R0.mapDiffeomorph A
    0 < a ∧ 16 / rho < a ^ 2 ∧ 8 < a ^ 2 ∧
    4 / a ^ 2 < rho / 4 ∧ 1 / a ^ 2 < 1 / 8 ∧
    EqOn G kappa (closedBall (0 : E2) 2) ∧
    EqOn G.symm kappa.symm (kappa '' closedBall (0 : E2) 2) ∧
    (∀ X : Set E2, X ⊆ closedBall (0 : E2) 2 → G '' X = kappa '' X) ∧
    (∀ p : (ℝ × ℝ) × ℝ,
      A p = L.symm (G (a • J2.symm p.1), c + r ^ 2 * a ^ 2 * p.2)) ∧
    (∀ y : E3, A.symm y =
      (J2 (a⁻¹ • G.symm (L y).1), ((L y).2 - c) / (r ^ 2 * a ^ 2))) ∧
    (∀ p : (ℝ × ℝ) × ℝ,
      ⟪(u : E3), A p⟫_ℝ = c + r ^ 2 * a ^ 2 * p.2) ∧
    ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ A.symm ∧
    ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ F.symm ∧
    (∀ y : E3, F y = A
      ((y 0 / Real.sqrt 2, y 1 / Real.sqrt 2),
        1 + y 2 - (y 1) ^ 2 + d ((y 0) ^ 2 + (y 1) ^ 2))) ∧
    (∀ y : E3,
      let s := J2 (a⁻¹ • G.symm (L y).1)
      let z := ((L y).2 - c) / (r ^ 2 * a ^ 2)
      F.symm y = !₂[Real.sqrt 2 * s.1, Real.sqrt 2 * s.2,
        z - 1 + 2 * s.2 ^ 2 - d (2 * (s.1 ^ 2 + s.2 ^ 2))]) ∧
    B.chart = F.toHomeomorph.toOpenPartialHomeomorph ∧
    B.chart.source = univ ∧ B.chart.target = univ ∧
    B.inside = A '' R0.inside ∧
    B.closedRegion = A '' R0.closedRegion ∧
    B.boundary = A '' R0.boundary ∧
    (∀ y : E3,
      let p := A.symm y
      let q := 2 * (p.1.1 ^ 2 + p.1.2 ^ 2)
      let N := q + (p.2 - 1 + 2 * p.1.2 ^ 2 - d q) ^ 2
      (y ∈ B.inside ↔ N < 1) ∧
      (y ∈ B.closedRegion ↔ N ≤ 1) ∧
      (y ∈ B.boundary ↔ N = 1)) ∧
    (∀ x ∈ closedBall (0 : E2) 2, ∀ t : ℝ,
      A.symm (L.symm (kappa x, t)) =
        (J2 (a⁻¹ • x), (t - c) / (r ^ 2 * a ^ 2))) ∧
    (∀ x ∈ closedBall (0 : E2) 2,
      (J2 (a⁻¹ • x)).1 ^ 2 + (J2 (a⁻¹ • x)).2 ^ 2 ≤ 4 / a ^ 2) ∧
    (∀ t : ℝ, |t - c| < r ^ 2 →
      |(t - c) / (r ^ 2 * a ^ 2)| < 1 / a ^ 2) ∧
    (∀ x ∈ closedBall (0 : E2) 2, ∀ t : ℝ, |t - c| < r ^ 2 →
      (L.symm (kappa x, t) ∈ B.inside ↔
        c + r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) < t) ∧
      (L.symm (kappa x, t) ∈ B.closedRegion ↔
        c + r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) ≤ t) ∧
      (L.symm (kappa x, t) ∈ B.boundary ↔
        c + r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = t)) := by
  classical
  let L := heightPlaneCoordinates u
  let R0 := nonnestedReferenceBallChart 0 d hd
  let S2 : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := {
    toFun := fun x => (2 : ℝ) • x
    invFun := fun x => (1 / 2 : ℝ) • x
    left_inv := fun x => by simp only [smul_smul]; norm_num
    right_inv := fun x => by simp only [smul_smul]; norm_num
    contMDiff_toFun := (contDiff_const.smul contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_const.smul contDiff_id).contMDiff }
  let e2 := S2.toHomeomorph.transOpenPartialHomeomorph kappa
  have he2 : ContDiffOn ℝ ∞ e2 e2.source :=
    hkappa.comp S2.contDiff.contDiffOn (fun _ hx => hx)
  have he2i : ContDiffOn ℝ ∞ e2.symm e2.target :=
    S2.symm.contDiff.comp_contDiffOn hkappaInv
  let B2 : BallNeighborhoodChart E2 E2 := {
    chart := e2
    closedBall_subset_source := by
      intro x hx
      apply hkappaSource
      change (2 : ℝ) • x ∈ closedBall (0 : E2) 2
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      have hn := mem_closedBall_zero_iff.mp hx
      linarith
    smooth := he2
    smooth_symm := he2i }
  obtain ⟨G2, hG2, _, _, _, _⟩ := exists_saddle_planar_ball_chart_extension B2
  let G := S2.symm.trans G2
  have hG : EqOn G kappa (closedBall (0 : E2) 2) := by
    intro x hx
    have hsmall : S2.symm x ∈ closedBall (0 : E2) 1 := by
      change (1 / 2 : ℝ) • x ∈ closedBall (0 : E2) 1
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      have hn := mem_closedBall_zero_iff.mp hx
      linarith
    change G2 (S2.symm x) = kappa x
    rw [hG2 hsmall]
    change kappa (S2 (S2.symm x)) = kappa x
    rw [S2.apply_symm_apply]
  have hGi : EqOn G.symm kappa.symm (kappa '' closedBall (0 : E2) 2) := by
    rintro y ⟨x, hx, rfl⟩
    have hix : G.symm (kappa x) = x := by rw [← hG hx, G.symm_apply_apply]
    exact hix.trans (kappa.left_inv (hkappaSource hx)).symm
  have hGX (X : Set E2) (hX : X ⊆ closedBall (0 : E2) 2) : G '' X = kappa '' X :=
    image_congr (fun _ hx => hG (hX hx))
  have hquot : 0 < (16 : ℝ) / rho := div_pos (by norm_num) hrho
  let a := Real.sqrt (16 / rho + 9)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 16 / rho + 9 := Real.sq_sqrt (by linarith)
  have haSq : 0 < a ^ 2 := sq_pos_of_pos ha
  have h16 : 16 / rho < a ^ 2 := by rw [ha2]; linarith
  have h8 : 8 < a ^ 2 := by rw [ha2]; linarith
  have hbudget : 16 < rho * a ^ 2 := by
    simpa only [mul_comm] using (div_lt_iff₀ hrho).mp h16
  have h4 : 4 / a ^ 2 < rho / 4 :=
    (div_lt_iff₀ haSq).mpr (by nlinarith)
  have h1 : 1 / a ^ 2 < 1 / 8 :=
    (div_lt_iff₀ haSq).mpr (by nlinarith)
  let v := r ^ 2 * a ^ 2
  have hv : 0 < v := mul_pos (sq_pos_of_pos hr) haSq
  let fA : (ℝ × ℝ) × ℝ → E3 := fun p =>
    L.symm (G (a • J2.symm p.1), c + v * p.2)
  let gA : E3 → (ℝ × ℝ) × ℝ := fun y =>
    (J2 (a⁻¹ • G.symm (L y).1), ((L y).2 - c) / v)
  have hAf : ContDiff ℝ ∞ fA := L.symm.contDiff.comp
    ((G.contDiff.comp ((contDiff_const (c := a)).smul
      (J2.symm.contDiff.comp contDiff_fst))).prodMk
        ((contDiff_const (c := c)).add ((contDiff_const (c := v)).mul contDiff_snd)))
  have hAg : ContDiff ℝ ∞ gA :=
    (J2.contDiff.comp ((contDiff_const (c := a⁻¹)).smul
      (G.symm.contDiff.comp (contDiff_fst.comp L.contDiff)))).prodMk
        (((contDiff_snd.comp L.contDiff).sub (contDiff_const (c := c))).div_const v)
  let A : Diffeomorph 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, E3)
      ((ℝ × ℝ) × ℝ) E3 ∞ := {
    toFun := fA
    invFun := gA
    left_inv := by
      intro p
      dsimp only [fA, gA]
      rw [L.apply_symm_apply, G.symm_apply_apply]
      apply Prod.ext
      · simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, J2.apply_symm_apply]
      · change (c + v * p.2 - c) / v = p.2
        field_simp [hv.ne']
        ring
    right_inv := by
      intro y
      apply L.injective
      dsimp only [fA, gA]
      rw [L.apply_symm_apply]
      apply Prod.ext
      · simp only [J2.symm_apply_apply, smul_smul, mul_inv_cancel₀ ha.ne', one_smul,
          G.apply_symm_apply]
      · change c + v * (((L y).2 - c) / v) = (L y).2
        field_simp [hv.ne']
        ring
    contMDiff_toFun := hAf.contMDiff
    contMDiff_invFun := hAg.contMDiff }
  have hAp (p : (ℝ × ℝ) × ℝ) :
      A p = L.symm (G (a • J2.symm p.1), c + r ^ 2 * a ^ 2 * p.2) := rfl
  have hAi (y : E3) : A.symm y =
      (J2 (a⁻¹ • G.symm (L y).1), ((L y).2 - c) / (r ^ 2 * a ^ 2)) := rfl
  have hHeight (p : (ℝ × ℝ) × ℝ) :
      ⟪(u : E3), A p⟫_ℝ = c + r ^ 2 * a ^ 2 * p.2 := by
    calc
      ⟪(u : E3), A p⟫_ℝ = (L (A p)).2 := (heightPlaneCoordinates_snd u (A p)).symm
      _ = c + r ^ 2 * a ^ 2 * p.2 := by rw [hAp, L.apply_symm_apply]
  let F := (nonnestedReferenceDiffeomorph 0 d hd).trans A
  let B := R0.mapDiffeomorph A
  have hFp (y : E3) : F y = A
      ((y 0 / Real.sqrt 2, y 1 / Real.sqrt 2),
        1 + y 2 - (y 1) ^ 2 + d ((y 0) ^ 2 + (y 1) ^ 2)) := by
    change A (nonnestedReferenceDiffeomorph 0 d hd y) = _
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1 y]
    simp only [zero_add]
  have hFi (y : E3) :
      let s := J2 (a⁻¹ • G.symm (L y).1)
      let z := ((L y).2 - c) / (r ^ 2 * a ^ 2)
      F.symm y = !₂[Real.sqrt 2 * s.1, Real.sqrt 2 * s.2,
        z - 1 + 2 * s.2 ^ 2 - d (2 * (s.1 ^ 2 + s.2 ^ 2))] := by
    change (nonnestedReferenceDiffeomorph 0 d hd).symm (A.symm y) = _
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 d hd).2, hAi]
    simp only [sub_zero]
  have hBs : B.chart.source = univ := by
    ext y
    constructor
    · intro _
      exact mem_univ y
    · intro _
      exact ⟨mem_univ y, mem_univ _⟩
  have hBt : B.chart.target = univ := by
    ext y
    constructor
    · intro _
      exact mem_univ y
    · intro _
      exact ⟨mem_univ y, mem_univ _⟩
  have hBchart : B.chart = F.toHomeomorph.toOpenPartialHomeomorph := by
    apply OpenPartialHomeomorph.ext
    · intro y
      rfl
    · intro y
      rfl
    · exact hBs
  have hBi : B.inside = A '' R0.inside := R0.mapDiffeomorph_inside A
  have hBc : B.closedRegion = A '' R0.closedRegion := R0.mapDiffeomorph_closedRegion A
  have hBb : B.boundary = A '' R0.boundary := R0.mapDiffeomorph_boundary A
  have himage (X : Set ((ℝ × ℝ) × ℝ)) (y : E3) :
      y ∈ A '' X ↔ A.symm y ∈ X := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa only [A.symm_apply_apply] using hp
    · intro hy
      exact ⟨A.symm y, hy, A.apply_symm_apply y⟩
  have hRegions (y : E3) :
      let p := A.symm y
      let q := 2 * (p.1.1 ^ 2 + p.1.2 ^ 2)
      let N := q + (p.2 - 1 + 2 * p.1.2 ^ 2 - d q) ^ 2
      (y ∈ B.inside ↔ N < 1) ∧
      (y ∈ B.closedRegion ↔ N ≤ 1) ∧
      (y ∈ B.boundary ↔ N = 1) := by
    dsimp only
    rw [hBi, hBc, hBb, himage, himage, himage]
    simpa only [sub_zero] using (nonnestedReferenceBallChart_regions 0 d hd).2.2 (A.symm y)
  have hLocal (x : E2) (hx : x ∈ closedBall (0 : E2) 2) (t : ℝ) :
      A.symm (L.symm (kappa x, t)) =
        (J2 (a⁻¹ • x), (t - c) / (r ^ 2 * a ^ 2)) := by
    have hix : G.symm (kappa x) = x := by rw [← hG hx, G.symm_apply_apply]
    rw [hAi, L.apply_symm_apply, hix]
  have hCoord (x : E2) : J2 (a⁻¹ • x) = ((J2 x).1 / a, (J2 x).2 / a) := by
    rw [map_smul]
    apply Prod.ext <;> dsimp <;> ring
  have hNorm (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      (J2 (a⁻¹ • x)).1 ^ 2 + (J2 (a⁻¹ • x)).2 ^ 2 ≤ 4 / a ^ 2 := by
    have hn : ‖x‖ ^ 2 ≤ 4 := by
      have hh := mem_closedBall_zero_iff.mp hx
      nlinarith [norm_nonneg x]
    rw [hJ2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    simpa only [mul_pow, inv_pow, div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right hn haSq.le
  have hTime (t : ℝ) (ht : |t - c| < r ^ 2) :
      |(t - c) / (r ^ 2 * a ^ 2)| < 1 / a ^ 2 := by
    change |(t - c) / v| < 1 / a ^ 2
    rw [abs_div, abs_of_pos hv]
    calc
      |t - c| / v < r ^ 2 / v := div_lt_div_of_pos_right ht hv
      _ = 1 / a ^ 2 := by dsimp only [v]; field_simp [hr.ne', ha.ne']
  have hScale (x : E2) :
      v * ((J2 (a⁻¹ • x)).1 ^ 2 - (J2 (a⁻¹ • x)).2 ^ 2) =
        r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) := by
    rw [hCoord]
    dsimp only [v]
    field_simp [ha.ne']
  have hEta (t : ℝ) : v * ((t - c) / (r ^ 2 * a ^ 2)) = t - c := by
    change v * ((t - c) / v) = t - c
    field_simp [hv.ne']
  have hBox (x : E2) (hx : x ∈ closedBall (0 : E2) 2) (t : ℝ)
      (ht : |t - c| < r ^ 2) :
      (L.symm (kappa x, t) ∈ B.inside ↔
        c + r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) < t) ∧
      (L.symm (kappa x, t) ∈ B.closedRegion ↔
        c + r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) ≤ t) ∧
      (L.symm (kappa x, t) ∈ B.boundary ↔
        c + r ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = t) := by
    rw [hBi, hBc, hBb, himage, himage, himage, hLocal x hx t]
    obtain ⟨hi, hc, hb⟩ := nonnestedReferenceBallChart_morse_box 0 d hd
      rho hrho hrhoSmall hdEq (J2 (a⁻¹ • x), (t - c) / (r ^ 2 * a ^ 2))
      ((hNorm x hx).trans_lt h4) (by simpa only [sub_zero] using (hTime t ht).trans h1)
    simp only [zero_add] at hi hc hb
    rw [hi, hc, hb]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro h
        have hh := mul_lt_mul_of_pos_left h hv
        rw [hScale, hEta] at hh
        linarith
      · intro h
        apply (mul_lt_mul_iff_right₀ hv).mp
        rw [hScale, hEta]
        linarith
    · constructor
      · intro h
        have hh := mul_le_mul_of_nonneg_left h hv.le
        rw [hScale, hEta] at hh
        linarith
      · intro h
        apply (mul_le_mul_iff_right₀ hv).mp
        rw [hScale, hEta]
        linarith
    · constructor
      · intro h
        have hh := congrArg (fun z : ℝ => v * z) h
        rw [hEta, hScale] at hh
        linarith
      · intro h
        apply mul_left_cancel₀ hv.ne'
        rw [hEta, hScale]
        linarith
  exact ⟨a, G, A, ha, h16, h8, h4, h1, hG, hGi, hGX, hAp, hAi, hHeight,
    A.contDiff, A.symm.contDiff, F.contDiff, F.symm.contDiff, hFp, hFi,
    hBchart, hBs, hBt, hBi, hBc, hBb, hRegions, hLocal, hNorm, hTime, hBox⟩

end PoincareConjecture.M25.Topology3D
