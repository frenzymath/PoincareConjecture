import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceLowerPlanarChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceEndAxis
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RoundProfileNativeModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace Matrix Pointwise

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1500000 in

theorem exists_nonnested_reference_lower_fixed_end
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (P : SurgeryCapProfile) (i : Fin 2) :
    let eps : ℝ := (![1, -1] : Fin 2 → ℝ) i
    let L := heightPlaneCoordinates u
    let F : E3 → E3 := fun y =>
      L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
        (nonnestedReferenceDiffeomorph 0 d hd y).2)
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let E := j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) ≤ -1 / 8}
    let sector := {y : E3 | 0 < eps * (J2 (L y).1).2}
    let D := {p : ℝ × ℝ | |p.2| < 7 / 16 ∧
      0 < 3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2}
    let V := {x : E2 | 0 < eps * (J2 x).2 ∧
      31 / 256 < 2 * ‖x‖ ^ 2 ∧ 2 * ‖x‖ ^ 2 < 255 / 256}
    let Psi : (ℝ × ℝ) → E2 := fun p =>
      J2.symm (p.1 / Real.sqrt 2,
        eps * Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2) / Real.sqrt 2)
    let Xi : E2 → (ℝ × ℝ) := fun x =>
      (Real.sqrt 2 * (J2 x).1, 1 / 2 - Real.sqrt (1 - 2 * ‖x‖ ^ 2))
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    ∃ (k : ℝ → ℝ) (T : OpenPartialHomeomorph (E2 × ℝ) E3),
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc (-9 / 64 : ℝ) (-7 / 64)) ∧
      EqOn k id (Icc (-17 / 128 : ℝ) (-15 / 128)) ∧
      let r : ℝ → ℝ := fun z => Real.sqrt (k z + 1 / 4)
      T.source = {p : E2 × ℝ | r p.2 • J2 p.1 ∈ D} ∧
      T.target = {y : E3 | (L y).1 ∈ V} ∧
      (∀ p : E2 × ℝ, T p = L.symm (Psi (r p.2 • J2 p.1), p.2)) ∧
      (∀ y : E3, T.symm y = (J2.symm ((r (H y))⁻¹ • Xi (L y).1), H y)) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
      ContDiffOn ℝ ∞ T T.source ∧
      ContDiffOn ℝ ∞ T.symm T.target ∧
      (∀ p ∈ T.source, H (T p) = p.2) ∧
      (∀ y ∈ T.target, (T.symm y).2 = H y) ∧
      (∀ z : ℝ, |z + 1 / 8| < 1 / 128 →
        T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          S ∩ {y | H y = z} ∩ sector) ∧
      ∀ lambda : ℝ, 0 < lambda → lambda * P.heightBound < 1 / 256 →
        let cap : E3 → E3 := fun y =>
          T ((M (heightCoordinates y)).1, -1 / 8 + lambda * (M (heightCoordinates y)).2)
        let north := cap '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
        ∃ A : BallNeighborhoodChart E3 E3,
          A.boundary = E ∪ north ∧
          A.closedRegion ⊆ F '' closedBall (0 : E3) 1 ∧
          A.closedRegion ⊆ sector ∧
          A.closedRegion ⊆ {y | H y ≤ -1 / 8 + lambda * P.heightBound} ∧
          (∀ s ∈ Icc (0 : ℝ) (1 / 128),
            let z := -1 / 8 - s
            A.inside ∩ {y | H y = z} =
              T '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
            A.closedRegion ∩ {y | H y = z} =
              T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
          (∀ q : UnitTwoSphere, -1 / 8 < (heightCoordinates (q : E3)).2 →
            cap (q : E3) ∈ A.boundary) := by
  classical
  dsimp only
  let eps : ℝ := (![1, -1] : Fin 2 → ℝ) i
  let L := heightPlaneCoordinates u
  let F : E3 → E3 := fun y => L.symm
    (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
      (nonnestedReferenceDiffeomorph 0 d hd y).2)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let S := range j
  let E := j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) ≤ -1 / 8}
  let sector := {y : E3 | 0 < eps * (J2 (L y).1).2}
  let D := {p : ℝ × ℝ | |p.2| < 7 / 16 ∧
    0 < 3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2}
  let V := {x : E2 | 0 < eps * (J2 x).2 ∧
    31 / 256 < 2 * ‖x‖ ^ 2 ∧ 2 * ‖x‖ ^ 2 < 255 / 256}
  obtain ⟨e, heS, heV, hef, hei, he, heiSmooth, heNorm, heBuffer⟩ :=
    exists_nonnested_reference_lower_planar_chart J2 hJ2 i
  change e.source = D at heS
  change e.target = V at heV
  change ∀ p : ℝ × ℝ, e p = J2.symm
    (p.1 / Real.sqrt 2, eps * Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2) /
      Real.sqrt 2) at hef
  have heps : eps ^ 2 = 1 := by fin_cases i <;> norm_num [eps]
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwoSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hH (y : E3) : (L y).2 = H y := heightPlaneCoordinates_snd u y
  have hHs (p : E2 × ℝ) : H (L.symm p) = p.2 := by
    rw [← hH, L.apply_symm_apply]
  let rho : ℝ × ℝ → ℝ := fun p => p.1 ^ 2 + p.2 ^ 2
  have hrho (a : ℝ) (x : E2) : rho (a • J2 x) = a ^ 2 * ‖x‖ ^ 2 := by
    dsimp [rho]; simp only [mul_pow]
    rw [← hJ2]; ring
  let Y : (ℝ × ℝ) → ℝ → E3 := fun p z => L.symm (e p, z)
  have hYh (p : ℝ × ℝ) (z : ℝ) : H (Y p z) = z := hHs _
  have hYp (p : ℝ × ℝ) (z : ℝ) : (L (Y p z)).1 = e p := by simp [Y]
  have heMap (p : ℝ × ℝ) (hp : p ∈ D) : e p ∈ V := by
    rw [← heV]; exact e.map_source (heS.symm ▸ hp)
  have hYsector (p : ℝ × ℝ) (hp : p ∈ D) (z : ℝ) : Y p z ∈ sector := by
    change 0 < eps * (J2 (L (Y p z)).1).2
    rw [hYp]; exact (heMap p hp).1

  have build (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hap : ∀ t, 0 < a t)
      (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
      ∃ Q : OpenPartialHomeomorph (E2 × ℝ) E3,
        Q.source = {p | a p.2 • J2 p.1 ∈ D} ∧
        Q.target = {y | (L y).1 ∈ V} ∧
        (∀ p, Q p = Y (a p.2 • J2 p.1) (g p.2)) ∧
        (∀ y, Q.symm y =
          (J2.symm ((a (g.symm (H y)))⁻¹ • e.symm (L y).1), g.symm (H y))) ∧
        ContDiffOn ℝ ∞ Q Q.source ∧ ContDiffOn ℝ ∞ Q.symm Q.target := by
    let U : Set (E2 × ℝ) := {p | a p.2 • J2 p.1 ∈ D}
    let Z : Set E3 := {y | (L y).1 ∈ V}
    let f : E2 × ℝ → E3 := fun p => Y (a p.2 • J2 p.1) (g p.2)
    let v : E3 → ℝ := fun y => g.symm (H y)
    let h : E3 → E2 × ℝ := fun y =>
      (J2.symm ((a (v y))⁻¹ • e.symm (L y).1), v y)
    have hscale : ContDiff ℝ ∞ (fun p : E2 × ℝ => a p.2 • J2 p.1) :=
      (ha.comp contDiff_snd).smul (J2.contDiff.comp contDiff_fst)
    have hU : IsOpen U := (heS ▸ e.open_source).preimage hscale.continuous
    have hZ : IsOpen Z := (heV ▸ e.open_target).preimage L.continuous.fst
    have hv : ContDiff ℝ ∞ v := g.symm.contDiff.comp H.contDiff
    have hai : ContDiff ℝ ∞ (fun y : E3 => (a (v y))⁻¹) :=
      (ha.comp hv).inv (fun y => (hap _).ne')
    have hf : ContDiffOn ℝ ∞ f U := L.symm.contDiff.comp_contDiffOn
      ((he.comp hscale.contDiffOn (fun _ hp => heS.symm ▸ hp)).prodMk
        (g.contDiff.comp contDiff_snd).contDiffOn)
    have hh : ContDiffOn ℝ ∞ h Z :=
      (J2.symm.contDiff.comp_contDiffOn (hai.contDiffOn.smul
        (heiSmooth.comp L.contDiff.fst.contDiffOn (fun _ hy => heV.symm ▸ hy)))).prodMk
          hv.contDiffOn
    have hmapf (p : E2 × ℝ) (hp : p ∈ U) : f p ∈ Z := by
      change (L (Y (a p.2 • J2 p.1) (g p.2))).1 ∈ V
      rw [hYp]; exact heMap _ hp
    have hmaph (y : E3) (hy : y ∈ Z) : h y ∈ U := by
      change a (v y) • J2 (J2.symm ((a (v y))⁻¹ • e.symm (L y).1)) ∈ D
      rw [J2.apply_symm_apply, smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul]
      rw [← heS]; exact e.map_target (heV.symm ▸ hy)
    have hhf (p : E2 × ℝ) (hp : p ∈ U) : h (f p) = p := by
      have hvf : v (f p) = p.2 := by dsimp [v, f]; rw [hYh, g.symm_apply_apply]
      apply Prod.ext
      · change J2.symm ((a (v (f p)))⁻¹ • e.symm (L (f p)).1) = p.1
        rw [hvf, hYp, e.left_inv (heS.symm ▸ hp), smul_smul,
          inv_mul_cancel₀ (hap _).ne', one_smul, J2.symm_apply_apply]
      · exact hvf
    have hfh (y : E3) (hy : y ∈ Z) : f (h y) = y := by
      apply L.injective
      dsimp only [f, h, Y]
      rw [L.apply_symm_apply]
      rw [J2.apply_symm_apply, smul_smul, mul_inv_cancel₀ (hap _).ne',
        one_smul, e.right_inv (heV.symm ▸ hy)]
      exact Prod.ext rfl ((g.apply_symm_apply (H y)).trans (hH y).symm)
    let Q : OpenPartialHomeomorph (E2 × ℝ) E3 :=
      { toFun := f, invFun := h, source := U, target := Z
        map_source' := hmapf, map_target' := hmaph, left_inv' := hhf, right_inv' := hfh
        open_source := hU, open_target := hZ
        continuousOn_toFun := hf.continuousOn, continuousOn_invFun := hh.continuousOn }
    exact ⟨Q, rfl, rfl, fun _ => rfl, fun _ => rfl, hf, hh⟩
  let G : E3 → E3 := fun y =>
    (nonnestedReferenceDiffeomorph 0 d hd).symm (J2 (L y).1, H y)
  have hFG (y : E3) : F (G y) = y := by
    dsimp [F, G]
    rw [(nonnestedReferenceDiffeomorph 0 d hd).apply_symm_apply,
      J2.symm_apply_apply, ← hH, Prod.eta, L.symm_apply_apply]
  have hYinv (p : ℝ × ℝ) (hp : p ∈ D) (z : ℝ) :
      G (Y p z) = !₂[p.1,
        eps * Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2),
        z - 1 / 4 + p.2 - rho p] := by
    have hd0 : d (2 * ((J2 (e p)).1 ^ 2 + (J2 (e p)).2 ^ 2)) = 0 := by
      apply hdZero; rw [hJ2]; linarith [(heMap p hp).2.1]
    dsimp [G]; rw [hYh, hYp, (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).2]
    rw [hd0, hef p]
    simp only [J2.apply_symm_apply]
    ext m; fin_cases m
    · change Real.sqrt 2 * (p.1 / Real.sqrt 2) = p.1
      field_simp [htwo.ne']
    · change Real.sqrt 2 * (eps * Real.sqrt _ / Real.sqrt 2) =
        eps * Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2)
      field_simp [htwo.ne']
    · change z - 0 - 1 + 2 * (eps * Real.sqrt _ / Real.sqrt 2) ^ 2 - 0 = _
      rw [div_pow, mul_pow, heps, htwoSq, Real.sq_sqrt hp.2.le]
      dsimp [rho]; ring
  have hYnorm (p : ℝ × ℝ) (hp : p ∈ D) (z : ℝ) :
      ‖G (Y p z)‖ ^ 2 = 1 + (z + 1 / 4 - rho p) *
        (2 * p.2 - 1 + (z + 1 / 4 - rho p)) := by
    rw [hYinv p hp z, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change p.1 ^ 2 + (eps * Real.sqrt _) ^ 2 + (z - 1 / 4 + p.2 - rho p) ^ 2 = _
    rw [mul_pow, heps, Real.sq_sqrt hp.2.le]
    dsimp [rho]; ring
  have hYsphere (p : ℝ × ℝ) (hp : p ∈ D) (z : ℝ)
      (hz : rho p = z + 1 / 4) :
      ∃ q : UnitTwoSphere, j q = Y p z ∧ 0 < eps * (q : E3) 1 := by
    have hn : ‖G (Y p z)‖ = 1 := by
      have hh := hYnorm p hp z; rw [hz] at hh
      nlinarith [norm_nonneg (G (Y p z))]
    refine ⟨⟨G (Y p z), mem_sphere_zero_iff_norm.mpr hn⟩, hFG _, ?_⟩
    change 0 < eps * (G (Y p z)) 1
    rw [hYinv p hp z]
    change 0 < eps * (eps * Real.sqrt _)
    have hr : 0 < Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2) := Real.sqrt_pos.2 hp.2
    rw [← mul_assoc, ← pow_two, heps, one_mul]
    exact hr
  have hjh (q : UnitTwoSphere) : H (j q) =
      1 + (q : E3) 2 - (q : E3) 1 ^ 2 + d ((q : E3) 0 ^ 2 + (q : E3) 1 ^ 2) := by
    dsimp [j, F]; rw [hHs, (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
    simp only [zero_add]
  have hjp (q : UnitTwoSphere) :
      J2 (L (j q)).1 = ((q : E3) 0 / Real.sqrt 2, (q : E3) 1 / Real.sqrt 2) := by
    dsimp [j, F]
    rw [L.apply_symm_apply, J2.apply_symm_apply,
      (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
  have hsgn (q : UnitTwoSphere) : j q ∈ sector ↔ 0 < eps * (q : E3) 1 := by
    change 0 < eps * (J2 (L (j q)).1).2 ↔ _
    rw [hjp, ← mul_div_assoc]
    exact div_pos_iff_of_pos_right htwo
  have hLow (q : UnitTwoSphere) (hh : H (j q) ≤ -7 / 64)
      (hsg : 0 < eps * (q : E3) 1) :
      ∃ p ∈ D, Y p (H (j q)) = j q ∧ rho p = H (j q) + 1 / 4 := by
    have hn : (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2 + (q : E3) 2 ^ 2 = 1 := by
      have h := congrArg (fun z : ℝ => z ^ 2) (norm_eq_of_mem_sphere q)
      simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, one_pow] using h
    let v : ℝ := (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have hw : -1 ≤ (q : E3) 2 := by nlinarith [sq_nonneg ((q : E3) 0), sq_nonneg ((q : E3) 1)]
    have hlarge : sigma < v := by
      by_contra hnle
      have hsmall : v ≤ 1 / 16 := (le_of_not_gt hnle).trans hsigmaSmall
      have hsq : v ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
        (sq_le_sq₀ hv (by norm_num)).2 hsmall
      have hb := (hdBounds v hv).1
      rw [hjh] at hh
      change 1 + (q : E3) 2 - (q : E3) 1 ^ 2 + d v ≤ -7 / 64 at hh
      dsimp [v] at *
      nlinarith [sq_nonneg ((q : E3) 0)]
    have hdv : d v = 0 := hdZero v hlarge.le
    let p : ℝ × ℝ := ((q : E3) 0, (q : E3) 2 + 1 / 2)
    have hrhoq : rho p = H (j q) + 1 / 4 := by
      rw [hjh]; change rho p = 1 + _ - _ + d v + _
      rw [hdv]; dsimp [rho, p]; nlinarith only [hn]
    have hp : p ∈ D := by
      rw [← heS]
      apply heBuffer (3 / 8) (by norm_num) (by norm_num)
      change rho p ≤ (3 / 8 : ℝ) ^ 2
      rw [hrhoq]; linarith
    have henergy : 3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2 = (q : E3) 1 ^ 2 := by
      dsimp [p]; nlinarith only [hn]
    have hroot : Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2) = eps * (q : E3) 1 := by
      apply (Real.sqrt_eq_iff_eq_sq hp.2.le hsg.le).2
      rw [henergy, mul_pow, heps, one_mul]
    refine ⟨p, hp, ?_, hrhoq⟩
    apply L.injective
    rw [L.apply_symm_apply]
    apply Prod.ext
    · apply J2.injective; rw [hef, J2.apply_symm_apply, hjp, hroot]
      dsimp only [p]
      apply Prod.ext
      · rfl
      · change eps * (eps * (q : E3) 1) / Real.sqrt 2 = (q : E3) 1 / Real.sqrt 2
        congr 1
        calc
          eps * (eps * (q : E3) 1) = eps ^ 2 * (q : E3) 1 := by ring
          _ = (q : E3) 1 := by rw [heps, one_mul]
    · exact (hH (j q)).symm
  obtain ⟨k, hk, hkr, hke⟩ := exists_saddle_end_height_clamp
    (-17 / 128) (-15 / 128) (1 / 128) (by norm_num) (by norm_num)
  have hkrange (z : ℝ) : k z ∈ Icc (-9 / 64 : ℝ) (-7 / 64) := by
    constructor <;> linarith [(hkr z).1, (hkr z).2]
  let r : ℝ → ℝ := fun z => Real.sqrt (k z + 1 / 4)
  have hrp (z : ℝ) : 0 < r z := Real.sqrt_pos.2 (by linarith [(hkrange z).1])
  have hrSq (z : ℝ) : r z ^ 2 = k z + 1 / 4 :=
    Real.sq_sqrt (by linarith [(hkrange z).1])
  have hrsm : ContDiff ℝ ∞ r :=
    (hk.add contDiff_const).sqrt (fun z => by linarith [(hkrange z).1])
  have hsource (z : ℝ) (x : E2) (hx : ‖x‖ ≤ 1) : r z • J2 x ∈ D := by
    rw [← heS]; apply heBuffer (3 / 8) (by norm_num) (by norm_num)
    change rho (r z • J2 x) ≤ (3 / 8 : ℝ) ^ 2
    rw [hrho]
    have hxSq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hh := mul_le_mul_of_nonneg_left hxSq (sq_nonneg (r z))
    rw [hrSq] at hh ⊢
    nlinarith [(hkrange z).2]
  obtain ⟨T, hTs, hTt, hTf, hTi, hTsm, hTism⟩ :=
    build r hrsm hrp (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hTc : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source := by
    rintro ⟨x, z⟩ ⟨hx, _⟩
    rw [hTs]; exact hsource z x (mem_closedBall_zero_iff.mp hx)
  have hTh (p : E2 × ℝ) : H (T p) = p.2 := by rw [hTf, hYh]; rfl
  have hkin (z : ℝ) (hz : |z + 1 / 8| < 1 / 128) : k z = z :=
    hke ⟨by linarith [(abs_lt.mp hz).1], by linarith [(abs_lt.mp hz).2]⟩
  have hcircle (z : ℝ) (hz : |z + 1 / 8| < 1 / 128) :
      T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z} ∩ sector := by
    ext y; constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = z := ht; subst t
      have hp := hsource z x (mem_sphere_zero_iff_norm.mp hx).le
      have hn : rho (r z • J2 x) = z + 1 / 4 := by
        rw [hrho, mem_sphere_zero_iff_norm.mp hx, one_pow, mul_one, hrSq, hkin z hz]
      obtain ⟨q, hq, _⟩ := hYsphere _ hp z hn
      refine ⟨⟨⟨q, ?_⟩, hTh _⟩, ?_⟩
      · rw [hTf]; exact hq
      · rw [hTf]; exact hYsector _ hp z
    · rintro ⟨⟨⟨q, rfl⟩, hqz⟩, hsec⟩
      obtain ⟨p, hp, hpy, hpn⟩ := hLow q
        (by rw [hqz]; linarith [(abs_lt.mp hz).2]) ((hsgn q).1 hsec)
      let x := J2.symm ((r z)⁻¹ • p)
      have hxp : r z • J2 x = p := by
        dsimp [x]; rw [J2.apply_symm_apply, smul_smul, mul_inv_cancel₀ (hrp z).ne', one_smul]
      have hxn : ‖x‖ ^ 2 = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 (hrp z).ne')
        rw [← hrho, hxp, hpn, hqz, mul_one, hrSq, hkin z hz]
      refine ⟨(x, z), ⟨mem_sphere_zero_iff_norm.mpr (by nlinarith [norm_nonneg x]), rfl⟩, ?_⟩
      rw [hTf, hxp]
      change Y p z = j q
      rwa [hqz] at hpy
  refine ⟨k, T, hk, hkrange, hke, hTs, hTt, ?_, ?_, hTc, hTsm, hTism,
    fun p _ => hTh p, ?_, hcircle, ?_⟩
  · intro p; rw [hTf]; exact congrArg L.symm (Prod.ext (hef _) rfl)
  · intro y; rw [hTi, hei]; rfl
  · intro y _; rw [hTi]; rfl
  intro lambda hlambda hsmall
  let M := flatCapDiffeomorph P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  let cap : E3 → E3 := fun y =>
    T ((M (heightCoordinates y)).1, -1 / 8 + lambda * (M (heightCoordinates y)).2)
  let north := cap '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  have hla : lambda < 1 / 256 :=
    (le_mul_of_one_le_right hlambda.le P.one_le_heightBound).trans_lt hsmall
  have hgap : 0 < 1 / 8 - lambda := by linarith
  obtain ⟨J, hJhem, hJbound, _, hJfiber⟩ := exists_round_profile_native_ball_model P
  obtain ⟨g, hg, _, hgm, _, hgr, hgm1, hg0⟩ :=
    exists_nonnested_reference_end_axis (-1 / 8) (1 / 8) lambda hlambda (by linarith)
  let chi : ℝ → ℝ := fun t => Real.smoothTransition (2 * t + 3 / 2)
  have hchi : ContDiff ℝ ∞ chi := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hchi0 (t : ℝ) (ht : t ≤ -3 / 4) : chi t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hquot : ContDiff ℝ ∞ (fun t : ℝ => chi t / (t + 1)) := by
    apply contDiff_iff_contDiffAt.mpr; intro t
    by_cases ht : t = -1
    · subst t
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < -3 / 4 by norm_num)] with s hs
      rw [hchi0 s hs.le, zero_div]
    · exact hchi.contDiffAt.div (contDiffAt_id.add contDiffAt_const)
        (by intro h; apply ht; linarith)
  let R : ℝ → ℝ := fun t => lambda + (1 / 8 - lambda) * (chi t / (t + 1))
  have hRsm : ContDiff ℝ ∞ R := contDiff_const.add (contDiff_const.mul hquot)
  have hRp (t : ℝ) : 0 < R t := by
    by_cases ht : t ≤ -3 / 4
    · simpa only [R, hchi0 t ht, zero_div, mul_zero, add_zero] using hlambda
    · have hden : 0 < t + 1 := by linarith [lt_of_not_ge ht]
      have hq : 0 ≤ chi t / (t + 1) :=
        div_nonneg (Real.smoothTransition.nonneg _) hden.le
      exact add_pos_of_pos_of_nonneg hlambda (mul_nonneg hgap.le hq)
  have hRlaw (t : ℝ) : (t + 1) * R t = g t + 1 / 4 := by
    by_cases ht : t = -1
    · subst t; rw [hgm1]; norm_num
    · rw [hg t]; change (t + 1) * R t =
        -1 / 8 + lambda * t - (1 / 8 - lambda) * (1 - chi t) + 1 / 4
      dsimp [R]
      field_simp [show t + 1 ≠ 0 by intro h; apply ht; linarith]
      ring
  let bot : ℝ → ℝ := fun t => Real.sqrt (R t / (1 - t)) / P.horizontal t
  let top : ℝ → ℝ := fun t => Real.sqrt (g t + 1 / 4)
  have htop (t : ℝ) (ht : -3 / 16 < t) : 0 < g t + 1 / 4 := by
    rw [hgr t (by linarith)]
    have hh := mul_lt_mul_of_pos_left ht hlambda
    nlinarith
  have hbot (t : ℝ) (ht : t < -1 / 16) : ContDiffAt ℝ ∞ bot t := by
    have hden : 0 < 1 - t := by linarith only [ht]
    exact ((hRsm.contDiffAt.div (contDiffAt_const.sub contDiffAt_id)
      hden.ne').sqrt (ne_of_gt (div_pos (hRp t) hden))).div
        P.horizontal_smooth.contDiffAt (P.horizontal_pos t).ne'
  have hagree (t : ℝ) (ht : t ∈ Ioo (-3 / 16 : ℝ) (-1 / 16)) : bot t = top t := by
    have hs : 0 < 1 - t ^ 2 := by
      have hh := mul_pos (show 0 < 1 - t by linarith [ht.2])
        (show 0 < 1 + t by linarith [ht.1])
      nlinarith only [hh]
    have hsSq := Real.sq_sqrt hs.le
    have hn : P.horizontal t = (Real.sqrt (1 - t ^ 2))⁻¹ :=
      P.horizontal_near t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hbSq : bot t ^ 2 = g t + 1 / 4 := by
      dsimp [bot]; rw [div_pow, Real.sq_sqrt (div_nonneg (hRp t).le (by linarith [ht.2])), hn,
        inv_pow, div_inv_eq_mul, hsSq]
      calc
        R t / (1 - t) * (1 - t ^ 2) = (t + 1) * R t := by
          field_simp [show 1 - t ≠ 0 by linarith [ht.2]]; ring
        _ = g t + 1 / 4 := hRlaw t
    have htSq : top t ^ 2 = g t + 1 / 4 := Real.sq_sqrt (htop t ht.1).le
    have hb0 : 0 ≤ bot t := div_nonneg (Real.sqrt_nonneg _) (P.horizontal_pos t).le
    have ht0 : 0 ≤ top t := Real.sqrt_nonneg _
    nlinarith only [hbSq, htSq, hb0, ht0]
  let a : ℝ → ℝ := fun t => if t < -1 / 8 then bot t else top t
  have hasm : ContDiff ℝ ∞ a := by
    apply contDiff_iff_contDiffAt.mpr; intro t
    by_cases ht : t < -1 / 8
    · apply (hbot t (by linarith)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact if_pos hs
    · have htt : -3 / 16 < t := by linarith [le_of_not_gt ht]
      apply ((g.contDiff.contDiffAt.add contDiffAt_const).sqrt
        (htop t htt).ne').congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds htt] with s hs
      dsimp [a]; split_ifs with hss
      · exact hagree s ⟨hs, by linarith⟩
      · rfl
  have hap (t : ℝ) : 0 < a t := by
    dsimp [a]; split_ifs with ht
    · exact div_pos (Real.sqrt_pos.2 (div_pos (hRp t) (by linarith))) (P.horizontal_pos t)
    · exact Real.sqrt_pos.2 (htop t (by linarith [le_of_not_gt ht]))
  have hatop (t : ℝ) (ht : -1 / 8 ≤ t) : a t = Real.sqrt (g t + 1 / 4) :=
    if_neg (not_lt.mpr ht)
  let rn : ℝ → ℝ := fun t => P.horizontal t * Real.sqrt (1 - t ^ 2)
  have hrn0 (t : ℝ) : 0 ≤ rn t := mul_nonneg (P.horizontal_pos t).le (Real.sqrt_nonneg _)
  have hasq (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 0) :
      a t ^ 2 * rn t ^ 2 = g t + 1 / 4 := by
    have hs : 0 ≤ 1 - t ^ 2 := by
      have hh := mul_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
        (show 0 ≤ 1 + t by linarith [ht.1])
      nlinarith only [hh]
    by_cases hb : t < -1 / 8
    · rw [show a t = bot t from if_pos hb]
      calc
        bot t ^ 2 * rn t ^ 2 = R t / (1 - t) * (1 - t ^ 2) := by
          dsimp [bot, rn]; rw [div_pow, mul_pow, Real.sq_sqrt hs,
            Real.sq_sqrt (div_nonneg (hRp t).le (by linarith [ht.2]))]
          field_simp [(P.horizontal_pos t).ne']
        _ = (t + 1) * R t := by
          field_simp [show 1 - t ≠ 0 by linarith [ht.2]]; ring
        _ = g t + 1 / 4 := hRlaw t
    · rw [hatop t (le_of_not_gt hb), Real.sq_sqrt (htop t (by linarith)).le]
      have hrn : rn t = 1 := by
        dsimp [rn]; rw [P.horizontal_near t (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)]
        have hr : 0 < 1 - t ^ 2 := by
          have hh := mul_pos (show 0 < 1 - t by linarith [ht.2])
            (show 0 < 1 + t by linarith [le_of_not_gt hb])
          nlinarith only [hh]
        exact inv_mul_cancel₀ (Real.sqrt_pos.2 hr).ne'
      rw [hrn, one_pow, mul_one]
  have hdata (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      rho (a (J y).2 • J2 (J y).1) ≤ g (J y).2 + 1 / 4 ∧
      -1 / 4 ≤ g (J y).2 ∧ g (J y).2 ≤ -1 / 8 + lambda * P.heightBound := by
    have hb := hJbound y hy
    have hlo := hgm.monotone hb.2.1
    have hhi := hgm.monotone hb.2.2
    rw [hgm1] at hlo
    rw [hgr P.heightBound (by linarith [P.one_le_heightBound])] at hhi
    refine ⟨?_, by linarith only [hlo], hhi⟩
    rw [hrho]
    by_cases ht : (J y).2 ≤ 0
    · have hm : J y ∈ (J '' closedBall (0 : E3) 1) ∩ {p | p.2 = (J y).2} :=
        ⟨⟨y, hy, rfl⟩, rfl⟩
      rw [(hJfiber (J y).2 ⟨hb.2.1, ht⟩).2.1] at hm
      obtain ⟨x, hx, heq⟩ := hm
      have hn : ‖(J y).1‖ ≤ rn (J y).2 := by
        have h := mem_closedBall_zero_iff.mp hx
        have hex : x = (J y).1 := congrArg Prod.fst heq
        simpa only [hex] using h
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (hrn0 _)).2 hn) (sq_nonneg (a (J y).2))
      rwa [hasq (J y).2 ⟨hb.2.1, ht⟩] at hh
    · have hn : ‖(J y).1‖ ^ 2 ≤ 1 := by nlinarith [hb.1, norm_nonneg (J y).1]
      have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg (a (J y).2))
      rw [mul_one, hatop _ (by linarith [lt_of_not_ge ht]),
        Real.sq_sqrt (htop _ (by linarith [lt_of_not_ge ht])).le] at hh
      rw [hatop _ (by linarith [lt_of_not_ge ht]),
        Real.sq_sqrt (htop _ (by linarith [lt_of_not_ge ht])).le]
      exact hh
  have hbuffer (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      a (J y).2 • J2 (J y).1 ∈ D := by
    rw [← heS]; apply heBuffer (3 / 8) (by norm_num) (by norm_num)
    change rho (a (J y).2 • J2 (J y).1) ≤ (3 / 8 : ℝ) ^ 2
    linarith [(hdata y hy).1, (hdata y hy).2.2]
  obtain ⟨Q, hQs, _, hQf, _, hQsm, hQism⟩ := build a hasm hap g
  let A : BallNeighborhoodChart E3 E3 :=
    { chart := J.toHomeomorph.toOpenPartialHomeomorph.trans Q
      closedBall_subset_source := fun y hy => ⟨mem_univ _, hQs.symm ▸ hbuffer y hy⟩
      smooth := hQsm.comp J.contDiff.contDiffOn (fun _ hy => hy.2)
      smooth_symm := J.symm.contDiff.comp_contDiffOn (hQism.mono inter_subset_left) }
  have hAf (y : E3) : A.chart y = Y (a (J y).2 • J2 (J y).1) (g (J y).2) := hQf _
  have hAh (y : E3) : H (A.chart y) = g (J y).2 := by rw [hAf, hYh]
  have hcontained : A.closedRegion ⊆ F '' closedBall (0 : E3) 1 := by
    rintro y ⟨v, hv, rfl⟩
    let p := a (J v).2 • J2 (J v).1
    let z := g (J v).2
    have hp : p ∈ D := hbuffer v hv
    have hdisk : rho p ≤ z + 1 / 4 := (hdata v hv).1
    have htopz : z < -31 / 256 := by linarith [(hdata v hv).2.2]
    have hrho0 : 0 ≤ rho p := by dsimp [rho]; positivity
    have hpb : p.2 ≤ 3 / 8 := by
      have habs : |p.2| ≤ 3 / 8 := by
        apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 8)).mp
        rw [sq_abs]; dsimp [rho] at hdisk
        nlinarith [sq_nonneg p.1]
      exact (le_abs_self _).trans habs
    have hprod : (z + 1 / 4 - rho p) * (2 * p.2 - 1 + (z + 1 / 4 - rho p)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hdisk) (by linarith)
    refine ⟨G (A.chart v), mem_closedBall_zero_iff.mpr ?_, hFG _⟩
    rw [hAf]
    have hn := hYnorm p hp z
    nlinarith [norm_nonneg (G (Y p z))]
  have hAsector : A.closedRegion ⊆ sector := by
    rintro y ⟨v, hv, rfl⟩; rw [hAf]; exact hYsector _ (hbuffer v hv) _
  have hAheight : A.closedRegion ⊆ {y | H y ≤ -1 / 8 + lambda * P.heightBound} := by
    rintro y ⟨v, hv, rfl⟩
    change H (A.chart v) ≤ -1 / 8 + lambda * P.heightBound
    rw [hAh]; exact (hdata v hv).2.2
  have hcap (q : UnitTwoSphere) (hq : 0 ≤ (heightCoordinates (q : E3)).2) :
      A.chart (q : E3) = cap (q : E3) := by
    have hJq := (hJhem q).2 hq
    have ht0 : 0 ≤ (P.model q).2 := by
      change 0 ≤ P.vertical _ * (heightCoordinates (q : E3)).2
      exact mul_nonneg (P.vertical_pos _).le hq
    have htM : (P.model q).2 ≤ P.heightBound := (abs_le.mp (P.height_bound q)).2
    have hlM := mul_le_mul_of_nonneg_left htM hlambda.le
    have hkg : k (g (P.model q).2) = g (P.model q).2 := by
      apply hke
      rw [hgr _ (by linarith)]
      exact ⟨by nlinarith, by linarith⟩
    have har : a (P.model q).2 = r (g (P.model q).2) := by
      rw [hatop _ (by linarith)]; dsimp [r]; rw [hkg]
    change A.chart (q : E3) = T ((P.model q).1, -1 / 8 + lambda * (P.model q).2)
    rw [hAf, hJq, har, ← hgr _ (by linarith), hTf]
    rfl
  have hAlower (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      A.chart (q : E3) ∈ E := by
    let t := (heightCoordinates (q : E3)).2
    have hJq := (hJhem q).1 hq
    have ht : t ∈ Icc (-1 : ℝ) 0 :=
      ⟨by simpa only [hJq] using (hJbound q (sphere_subset_closedBall q.property)).2.1, hq⟩
    have hm : J (q : E3) ∈ (J '' sphere (0 : E3) 1) ∩ {p | p.2 = t} :=
      ⟨⟨q, q.property, rfl⟩, by
        change (J (q : E3)).2 = (heightCoordinates (q : E3)).2
        rw [hJq]⟩
    rw [(hJfiber t ht).2.2] at hm
    obtain ⟨x, hx, hxJ⟩ := hm
    have hp : a t • J2 x ∈ D := by
      have hh := hbuffer q (sphere_subset_closedBall q.property)
      simpa only [← hxJ] using hh
    have hr : rho (a t • J2 x) = g t + 1 / 4 := by
      rw [hrho, mem_sphere_zero_iff_norm.mp hx, hasq t ht]
    obtain ⟨q', hq', hsign⟩ := hYsphere _ hp _ hr
    have hqt : g t ≤ -1 / 8 := by simpa only [hg0] using hgm.monotone ht.2
    refine ⟨q', ⟨hsign, ?_⟩, ?_⟩
    · rw [hq', hYh]; exact hqt
    · rw [hAf, ← hxJ]; exact hq'
  have hback (y : E3) (hy : y ∈ E) : y ∈ A.boundary := by
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨p, hp, hpy, hpn⟩ := hLow q (by linarith [hq.2]) hq.1
    let t := g.symm (H (j q))
    have hgt : g t = H (j q) := g.apply_symm_apply _
    have hrho0 : 0 ≤ rho p := by dsimp [rho]; positivity
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor
      · apply hgm.le_iff_le.mp; rw [hgm1, hgt]; linarith
      · apply hgm.le_iff_le.mp; rw [hgt, hg0]; exact hq.2
    let x := J2.symm ((a t)⁻¹ • p)
    have hxp : a t • J2 x = p := by
      dsimp [x]; rw [J2.apply_symm_apply, smul_smul, mul_inv_cancel₀ (hap t).ne', one_smul]
    have hxn : ‖x‖ = rn t := by
      have hs : ‖x‖ ^ 2 = rn t ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 (hap t).ne')
        rw [← hrho, hxp, hpn, hasq t ht, hgt]
      nlinarith only [hs, norm_nonneg x, hrn0 t]
    have hm : (x, t) ∈ (J '' sphere (0 : E3) 1) ∩ {p | p.2 = t} := by
      rw [(hJfiber t ht).2.2]
      exact ⟨x, mem_sphere_zero_iff_norm.mpr hxn, rfl⟩
    obtain ⟨v, hv, hvJ⟩ := hm.1
    refine ⟨v, hv, ?_⟩
    rw [hAf, hvJ, hxp, hgt]
    exact hpy
  have hboundary : A.boundary = E ∪ north := by
    ext y; constructor
    · rintro ⟨v, hv, rfl⟩
      let q : UnitTwoSphere := ⟨v, hv⟩
      by_cases hq : (heightCoordinates v).2 ≤ 0
      · exact Or.inl (hAlower q hq)
      · right
        exact ⟨v, ⟨mem_sphere_zero_iff_norm.mp hv, (lt_of_not_ge hq).le⟩,
          (hcap q (lt_of_not_ge hq).le).symm⟩
    · rintro (hy | hy)
      · exact hback y hy
      · obtain ⟨v, ⟨hv, hh⟩, rfl⟩ := hy
        exact ⟨v, mem_sphere_zero_iff_norm.mpr hv, hcap ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩ hh⟩
  have imageFiber (K : Set E3) (B : Set E2) (t : ℝ)
      (hfib : (J '' K) ∩ {p | p.2 = t} = (fun x : E2 => (x, t)) '' B) :
      (A.chart '' K) ∩ {y | H y = g t} =
        (fun x : E2 => Y (a t • J2 x) (g t)) '' B := by
    ext y; constructor
    · rintro ⟨⟨v, hv, rfl⟩, hh⟩
      change H (A.chart v) = g t at hh
      have ht : (J v).2 = t := hgm.injective (by rwa [hAh] at hh)
      have hm : J v ∈ (J '' K) ∩ {p | p.2 = t} := ⟨⟨v, hv, rfl⟩, ht⟩
      rw [hfib] at hm
      obtain ⟨x, hx, heq⟩ := hm
      refine ⟨x, hx, ?_⟩; rw [hAf, ← heq]
    · rintro ⟨x, hx, rfl⟩
      have hm : (x, t) ∈ (J '' K) ∩ {p | p.2 = t} := by
        rw [hfib]; exact ⟨x, hx, rfl⟩
      obtain ⟨v, hv, heq⟩ := hm.1
      refine ⟨⟨v, hv, ?_⟩, hYh _ _⟩
      rw [hAf, heq]
  have hfibers (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 / 128)) :
      A.inside ∩ {y | H y = -1 / 8 - s} =
        T '' (ball (0 : E2) 1 ×ˢ ({-1 / 8 - s} : Set ℝ)) ∧
      A.closedRegion ∩ {y | H y = -1 / 8 - s} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({-1 / 8 - s} : Set ℝ)) := by
    let z : ℝ := -1 / 8 - s
    let t : ℝ := g.symm z
    have hgt : g t = z := g.apply_symm_apply _
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hgm.le_iff_le.mp <;> rw [hgt]
      · rw [hgm1]; dsimp [z]; linarith [hs.2]
      · rw [hg0]; dsimp [z]; linarith [hs.1]
    have htm : -1 < t := by
      apply hgm.lt_iff_lt.mp; rw [hgm1, hgt]; dsimp [z]; linarith [hs.2]
    have hrnp : 0 < rn t := by
      apply mul_pos (P.horizontal_pos t)
      apply Real.sqrt_pos.2
      have hh := mul_pos (show 0 < 1 - t by linarith [ht.2])
        (show 0 < 1 + t by linarith)
      nlinarith only [hh]
    have hkz : k z = z := hke ⟨by dsimp [z]; linarith [hs.2],
      by dsimp [z]; linarith [hs.1]⟩
    have hprod : a t * rn t = r z := by
      apply (sq_eq_sq₀ (mul_pos (hap t) hrnp).le (hrp z).le).mp
      rw [mul_pow, hasq t ht, hgt, hrSq, hkz]
    have hscale (B : Set E2) :
        (fun x : E2 => Y (a t • J2 x) z) '' ((fun w : E2 => rn t • w) '' B) =
          T '' (B ×ˢ ({z} : Set ℝ)) := by
      rw [image_image]
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨(x, z), ⟨hx, rfl⟩, ?_⟩
        rw [hTf]
        change Y (r z • J2 x) z = Y (a t • J2 (rn t • x)) z
        rw [map_smul, smul_smul, hprod]
      · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
        have hw' : w = z := hw; subst w
        refine ⟨x, hx, ?_⟩
        rw [hTf]
        change Y (a t • J2 (rn t • x)) z = Y (r z • J2 x) z
        rw [map_smul, smul_smul, hprod]
    have hball : (fun x : E2 => rn t • x) '' ball (0 : E2) 1 = ball 0 (rn t) := by
      rw [image_smul, _root_.smul_ball hrnp.ne', smul_zero, Real.norm_eq_abs,
        abs_of_pos hrnp, mul_one]
    have hclosed : (fun x : E2 => rn t • x) '' closedBall (0 : E2) 1 =
        closedBall 0 (rn t) := by
      rw [image_smul, smul_closedBall' hrnp.ne', smul_zero, Real.norm_eq_abs,
        abs_of_pos hrnp, mul_one]
    have ho := imageFiber (ball (0 : E3) 1) (ball (0 : E2) (rn t)) t (hJfiber t ht).1
    have hc := imageFiber (closedBall (0 : E3) 1) (closedBall (0 : E2) (rn t))
      t (hJfiber t ht).2.1
    rw [hgt, ← hball, hscale] at ho
    rw [hgt, ← hclosed, hscale] at hc
    exact ⟨ho, hc⟩
  refine ⟨A, hboundary, hcontained, hAsector, hAheight, hfibers, ?_⟩
  intro q hq
  by_cases hq0 : 0 ≤ (heightCoordinates (q : E3)).2
  · rw [hboundary]; right
    exact ⟨q, ⟨norm_eq_of_mem_sphere q, hq0⟩, rfl⟩
  · have hqneg : (heightCoordinates (q : E3)).2 < 0 := lt_of_not_ge hq0
    have hmodel : P.model q =
        ((circleDirection (heightCoordinates (q : E3)).1 : E2),
          (heightCoordinates (q : E3)).2) :=
      surgeryCapModel_cylinder P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        P.horizontal_near P.vertical_far q (abs_le.mpr ⟨by linarith, by linarith⟩)
    let z : ℝ := -1 / 8 + lambda * (heightCoordinates (q : E3)).2
    have hz : |z + 1 / 8| < 1 / 128 := by
      apply abs_lt.mpr
      have hlo := mul_lt_mul_of_pos_left hq hlambda
      have hhi := mul_neg_of_pos_of_neg hlambda hqneg
      change -(1 / 128) < -1 / 8 + lambda * (heightCoordinates (q : E3)).2 + 1 / 8 ∧
        -1 / 8 + lambda * (heightCoordinates (q : E3)).2 + 1 / 8 < 1 / 128
      constructor <;> nlinarith only [hlo, hhi, hla]
    have hc : cap (q : E3) ∈ T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
      refine ⟨((circleDirection (heightCoordinates (q : E3)).1 : E2), z),
        ⟨(circleDirection (heightCoordinates (q : E3)).1).property, rfl⟩, ?_⟩
      change T _ = T ((P.model q).1, -1 / 8 + lambda * (P.model q).2)
      rw [hmodel]
    rw [hcircle z hz] at hc
    rw [hboundary]; left
    obtain ⟨q', hq'⟩ := hc.1.1
    refine ⟨q', ⟨(hsgn q').1 (hq'.symm ▸ hc.2), ?_⟩, hq'⟩
    rw [hq', hc.1.2]
    change -1 / 8 + lambda * (heightCoordinates (q : E3)).2 ≤ -1 / 8
    have hhi := mul_neg_of_pos_of_neg hlambda hqneg
    linarith only [hhi]

end PoincareConjecture.M25.Topology3D
