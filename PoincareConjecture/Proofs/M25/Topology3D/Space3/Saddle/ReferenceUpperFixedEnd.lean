import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceQuarticChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceEndAxis
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RoundProfileNativeModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallBoundaryContainment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.AffineFlow
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace Matrix Pointwise NNReal

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in



theorem exists_nonnested_reference_upper_fixed_end
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (P : SurgeryCapProfile) :
    let L := heightPlaneCoordinates u
    let F : E3 → E3 := fun y =>
      L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
        (nonnestedReferenceDiffeomorph 0 d hd y).2)
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let E := j '' {q : UnitTwoSphere | 3 / 2 ≤ H (j q)}
    let f : ℝ → ℝ → ℝ := fun b t => t * Real.sqrt (b + t ^ 2)
    let v : ℝ → ℝ → ℝ := fun b Y =>
      Real.sqrt 2 * Y / Real.sqrt (b + Real.sqrt (b ^ 2 + 4 * Y ^ 2))
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    ∃ (k : ℝ → ℝ) (T : OpenPartialHomeomorph (E2 × ℝ) E3),
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc (5 / 4 : ℝ) (7 / 4)) ∧
      EqOn k id (Icc (11 / 8 : ℝ) (13 / 8)) ∧
      let b : ℝ → ℝ := fun z => 2 * k z - 1
      let C : ℝ → ℝ := fun z => k z * (2 - k z)
      T.source = univ ∧ T.target = univ ∧
      (∀ p : E2 × ℝ, T p = L.symm
        (J2.symm (Real.sqrt (C p.2) * (J2 p.1).1 / Real.sqrt 2,
          v (b p.2) (Real.sqrt (C p.2) * (J2 p.1).2) / Real.sqrt 2), p.2)) ∧
      (∀ y : E3, T.symm y =
        (J2.symm (Real.sqrt 2 * (J2 (L y).1).1 / Real.sqrt (C (H y)),
          f (b (H y)) (Real.sqrt 2 * (J2 (L y).1).2) / Real.sqrt (C (H y))), H y)) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
      ContDiffOn ℝ ∞ T T.source ∧
      ContDiffOn ℝ ∞ T.symm T.target ∧
      (∀ p ∈ T.source, H (T p) = p.2) ∧
      (∀ y ∈ T.target, (T.symm y).2 = H y) ∧
      (∀ z : ℝ, |z - 3 / 2| < 1 / 128 →
        T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z}) ∧
      ∀ lambda : ℝ, 0 < lambda → lambda * P.heightBound < 1 / 256 →
        let cap : E3 → E3 := fun y =>
          T ((M (heightCoordinates y)).1, 3 / 2 - lambda * (M (heightCoordinates y)).2)
        let north := cap '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
        ∃ A : BallNeighborhoodChart E3 E3,
          A.boundary = E ∪ north ∧
          A.closedRegion ⊆ F '' closedBall (0 : E3) 1 ∧
          A.closedRegion ⊆ {y | 3 / 2 - lambda * P.heightBound ≤ H y} ∧
          (∀ s ∈ Icc (0 : ℝ) (1 / 128),
            let z := 3 / 2 + s
            A.inside ∩ {y | H y = z} =
              T '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
            A.closedRegion ∩ {y | H y = z} =
              T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
          (∀ q : UnitTwoSphere, -1 / 8 < (heightCoordinates (q : E3)).2 →
            cap (q : E3) ∈ A.boundary) := by
  classical
  dsimp only
  let L := heightPlaneCoordinates u
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let W := (J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph.trans
    L.symm.toDiffeomorph
  let F := (nonnestedReferenceDiffeomorph 0 d hd).trans W
  let F0 := (nonnestedReferenceDiffeomorph 0 (fun _ => 0) contDiff_const).trans W
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let j0 : UnitTwoSphere → E3 := fun q => F0 (q : E3)
  let S := range j
  let E := j '' {q : UnitTwoSphere | 3 / 2 ≤ H (j q)}
  let E0 := j0 '' {q : UnitTwoSphere | 3 / 2 ≤ H (j0 q)}
  let f : ℝ → ℝ → ℝ := fun b t => t * Real.sqrt (b + t ^ 2)
  let v : ℝ → ℝ → ℝ := fun b Y =>
    Real.sqrt 2 * Y / Real.sqrt (b + Real.sqrt (b ^ 2 + 4 * Y ^ 2))
  let rr : ℝ × ℝ → ℝ := fun p => p.1 ^ 2 + p.2 ^ 2
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwoSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hH (y : E3) : (L y).2 = H y := heightPlaneCoordinates_snd u y
  have hHs (p : E2 × ℝ) : H (L.symm p) = p.2 := by rw [← hH, L.apply_symm_apply]
  have hrr (a : ℝ) (x : E2) : rr (a • J2 x) = a ^ 2 * ‖x‖ ^ 2 := by
    dsimp [rr]; simp only [mul_pow]
    rw [← hJ2]; ring
  obtain ⟨e, heS, heT, hef, hei, _he, heI, heSq, _⟩ :=
    exists_nonnested_reference_quartic_chart
  have hfv (b : ℝ) (hb : 0 < b) (Y : ℝ) : f b (v b Y) = Y := by
    have hh := congrArg Prod.snd (e.right_inv (x := (b, Y)) (heT.symm ▸ hb))
    simpa only [hei, hef] using hh
  have hvf (b : ℝ) (hb : 0 < b) (t : ℝ) : v b (f b t) = t := by
    have hh := congrArg Prod.snd (e.left_inv (x := (b, t)) (heS.symm ▸ hb))
    simpa only [hef, hei] using hh
  have hfsq (b : ℝ) (hb : 0 < b) (t : ℝ) :
      (f b t) ^ 2 = t ^ 2 * (b + t ^ 2) := by
    simpa only [hef] using heSq (b, t) (heS.symm ▸ hb)
  let Y : ℝ → (ℝ × ℝ) → ℝ → E3 := fun b p z =>
    L.symm (J2.symm (p.1 / Real.sqrt 2, v b p.2 / Real.sqrt 2), z)
  have hYh (b : ℝ) (p : ℝ × ℝ) (z : ℝ) : H (Y b p z) = z := hHs _
  have hYp (b : ℝ) (p : ℝ × ℝ) (z : ℝ) :
      J2 (L (Y b p z)).1 = (p.1 / Real.sqrt 2, v b p.2 / Real.sqrt 2) := by
    simp only [Y, L.apply_symm_apply, J2.apply_symm_apply]
  have build (a b : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
      (hap : ∀ t, 0 < a t) (hbp : ∀ t, 0 < b t)
      (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
      ∃ Q : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) (E2 × ℝ) E3 ∞,
        (∀ p, Q p = Y (b p.2) (a p.2 • J2 p.1) (g p.2)) ∧
        (∀ y, Q.symm y =
          (J2.symm ((a (g.symm (H y)))⁻¹ •
            (Real.sqrt 2 * (J2 (L y).1).1,
              f (b (g.symm (H y))) (Real.sqrt 2 * (J2 (L y).1).2))), g.symm (H y))) := by
    let A : E2 × ℝ → E3 := fun p => Y (b p.2) (a p.2 • J2 p.1) (g p.2)
    let t : E3 → ℝ := fun y => g.symm (H y)
    let B : E3 → E2 × ℝ := fun y =>
      (J2.symm ((a (t y))⁻¹ • (Real.sqrt 2 * (J2 (L y).1).1,
        f (b (t y)) (Real.sqrt 2 * (J2 (L y).1).2))), t y)
    have hscale : ContDiff ℝ ∞ (fun p : E2 × ℝ => a p.2 • J2 p.1) :=
      (ha.comp contDiff_snd).smul (J2.contDiff.comp contDiff_fst)
    have hvsm : ContDiff ℝ ∞ (fun p : E2 × ℝ => v (b p.2) (a p.2 • J2 p.1).2) := by
      apply contDiffOn_univ.mp
      have hc : ContDiffOn ℝ ∞
          (fun p : E2 × ℝ => e.symm (b p.2, (a p.2 • J2 p.1).2)) univ :=
        heI.comp ((hb.comp contDiff_snd).prodMk hscale.snd).contDiffOn
          (fun p _ => heT.symm ▸ hbp p.2)
      simpa only [hei] using hc.snd
    have hA : ContDiff ℝ ∞ A := L.symm.contDiff.comp
      ((J2.symm.contDiff.comp ((hscale.fst.div_const _).prodMk
        (hvsm.div_const _))).prodMk (g.contDiff.comp contDiff_snd))
    have ht : ContDiff ℝ ∞ t := g.symm.contDiff.comp H.contDiff
    have hn : ContDiff ℝ ∞ (fun y : E3 => Real.sqrt 2 * (J2 (L y).1).2) := by fun_prop
    have hff : ContDiff ℝ ∞ (fun y : E3 => f (b (t y)) (Real.sqrt 2 * (J2 (L y).1).2)) :=
      hn.mul (((hb.comp ht).add (hn.pow 2)).sqrt (fun y => by
        have := hbp (t y); positivity))
    have hB : ContDiff ℝ ∞ B := (J2.symm.contDiff.comp
      (((ha.comp ht).inv (fun y => (hap _).ne')).smul
        ((by fun_prop : ContDiff ℝ ∞ (fun y : E3 => Real.sqrt 2 * (J2 (L y).1).1)).prodMk
          hff))).prodMk ht
    have hBA (p : E2 × ℝ) : B (A p) = p := by
      have htA : t (A p) = p.2 := by dsimp [t, A]; rw [hYh, g.symm_apply_apply]
      apply Prod.ext
      · change J2.symm ((a (t (A p)))⁻¹ •
          (Real.sqrt 2 * (J2 (L (A p)).1).1,
            f (b (t (A p))) (Real.sqrt 2 * (J2 (L (A p)).1).2))) = p.1
        rw [htA, hYp]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have hc (s : ℝ) : Real.sqrt 2 * (s / Real.sqrt 2) = s := by field_simp [htwo.ne']
        rw [hc, hc, hfv _ (hbp _) _]
        apply J2.injective; rw [J2.apply_symm_apply]
        ext <;> dsimp <;> field_simp [(hap p.2).ne']
      · exact htA
    have hAB (y : E3) : A (B y) = y := by
      apply L.injective; apply Prod.ext
      · apply J2.injective
        change J2 (L (Y (b (t y)) (a (t y) • J2 (B y).1) (g (t y)))).1 = J2 (L y).1
        rw [hYp]
        dsimp only [B]
        rw [J2.apply_symm_apply, smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul]
        rw [hvf _ (hbp _) _]
        ext <;> dsimp <;> field_simp [htwo.ne']
      · rw [hH, hH]
        change H (Y (b (t y)) (a (t y) • J2 (B y).1) (g (t y))) = H y
        rw [hYh]; exact g.apply_symm_apply (H y)
    let Q : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) (E2 × ℝ) E3 ∞ :=
      { toEquiv := { toFun := A, invFun := B, left_inv := hBA, right_inv := hAB }
        contMDiff_toFun := hA.contMDiff, contMDiff_invFun := hB.contMDiff }
    exact ⟨Q, fun _ => rfl, fun _ => rfl⟩
  let q : E3 → ℝ := fun y => 2 * ‖(L y).1‖ ^ 2
  let eta : E3 → ℝ := fun y => Real.sqrt 2 * (J2 (L y).1).2
  have hq0 (y : E3) : 0 ≤ q y := by dsimp [q]; positivity
  have heta (y : E3) : (eta y) ^ 2 ≤ q y := by
    dsimp [eta, q]; rw [mul_pow, htwoSq, ← hJ2]
    nlinarith only [sq_nonneg (J2 (L y).1).1]
  have hFn (y : E3) : ‖F.symm y‖ ^ 2 = q y + (H y - 1 + eta y ^ 2 - d (q y)) ^ 2 := by
    change ‖(nonnestedReferenceDiffeomorph 0 d hd).symm (J2 (L y).1, (L y).2)‖ ^ 2 = _
    rw [hH, (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).2,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    dsimp [q, eta]; rw [← hJ2]
    simp only [mul_pow, htwoSq, sub_zero]; ring
  have hF0n (y : E3) : ‖F0.symm y‖ ^ 2 = q y + (H y - 1 + eta y ^ 2) ^ 2 := by
    change ‖(nonnestedReferenceDiffeomorph 0 (fun _ => 0) contDiff_const).symm
      (J2 (L y).1, (L y).2)‖ ^ 2 = _
    rw [hH, (nonnestedReferenceDiffeomorph_apply_symm 0 (fun _ => 0) contDiff_const).2,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    dsimp [q, eta]; rw [← hJ2]
    simp only [mul_pow, htwoSq, sub_zero]; ring
  have hYn (p : ℝ × ℝ) (z : ℝ) (hz : 0 < 2 * z - 1) :
      ‖F0.symm (Y (2 * z - 1) p z)‖ ^ 2 = 1 + rr p - z * (2 - z) := by
    rw [hF0n, hYh]
    have hsq := hfsq (2 * z - 1) hz (v (2 * z - 1) p.2)
    rw [hfv _ hz] at hsq
    dsimp [q, eta]; rw [← hJ2, hYp]
    simp only [mul_pow, div_pow, htwoSq]
    dsimp [rr]; nlinarith only [hsq]
  have hsmallNorm (y : E3) (hz : H y ∈ Icc (11 / 8 : ℝ) (13 / 8))
      (hy : q y ≤ sigma) : ‖F.symm y‖ < 1 ∧ ‖F0.symm y‖ < 1 := by
    have hq : q y ≤ 1 / 16 := hy.trans hsigmaSmall
    have hsig2 : sigma ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := (sq_le_sq₀ hsigma.le (by norm_num)).2 hsigmaSmall
    have hq2 : q y ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
      ((sq_le_sq₀ (hq0 y) hsigma.le).2 hy).trans hsig2
    have hdq := hdBounds (q y) (hq0 y)
    have hw : 0 ≤ H y - 1 + eta y ^ 2 - d (q y) ∧
        H y - 1 + eta y ^ 2 - d (q y) < 3 / 4 := by
      constructor <;> nlinarith only [hz.1, hz.2, heta y, sq_nonneg (eta y), hdq.1, hdq.2, hq2, hq]
    have hw0 : 0 ≤ H y - 1 + eta y ^ 2 ∧ H y - 1 + eta y ^ 2 < 3 / 4 := by
      constructor <;> nlinarith only [hz.1, hz.2, heta y, sq_nonneg (eta y), hq]
    have hw2 := (sq_lt_sq₀ hw.1 (by norm_num : (0 : ℝ) ≤ 3 / 4)).2 hw.2
    have hw02 := (sq_lt_sq₀ hw0.1 (by norm_num : (0 : ℝ) ≤ 3 / 4)).2 hw0.2
    constructor <;> nlinarith only [hFn y, hF0n y, hq, hw2, hw02, norm_nonneg (F.symm y),
      norm_nonneg (F0.symm y)]
  have hband (y : E3) (hz : H y ∈ Icc (11 / 8 : ℝ) (13 / 8)) :
      (‖F.symm y‖ = 1 ↔ ‖F0.symm y‖ = 1) ∧
      (‖F0.symm y‖ ≤ 1 → ‖F.symm y‖ ≤ 1) := by
    by_cases hq : sigma ≤ q y
    · have hh : ‖F.symm y‖ = ‖F0.symm y‖ := by
        have hn := hFn y; rw [hdZero _ hq, sub_zero, ← hF0n] at hn
        nlinarith only [hn, norm_nonneg (F.symm y), norm_nonneg (F0.symm y)]
      rw [hh]; exact ⟨Iff.rfl, id⟩
    · have hh := hsmallNorm y hz (le_of_not_ge hq)
      exact ⟨iff_of_false (ne_of_lt hh.1) (ne_of_lt hh.2), fun _ => hh.1.le⟩
  have hS (y : E3) : y ∈ S ↔ ‖F.symm y‖ = 1 := by
    constructor
    · rintro ⟨p, rfl⟩; simpa only [j, F.symm_apply_apply] using norm_eq_of_mem_sphere p
    · intro hy; exact ⟨⟨F.symm y, mem_sphere_zero_iff_norm.mpr hy⟩, F.apply_symm_apply y⟩
  obtain ⟨k, hk, hkr, hke⟩ := exists_saddle_end_height_clamp
    (11 / 8) (13 / 8) (1 / 8) (by norm_num) (by norm_num)
  change ∀ ⦃z : ℝ⦄, z ∈ Icc (11 / 8 : ℝ) (13 / 8) → k z = z at hke
  have hkrange (z : ℝ) : k z ∈ Icc (5 / 4 : ℝ) (7 / 4) := by
    constructor <;> linarith [(hkr z).1, (hkr z).2]
  let b : ℝ → ℝ := fun z => 2 * k z - 1
  let C : ℝ → ℝ := fun z => k z * (2 - k z)
  let r : ℝ → ℝ := fun z => Real.sqrt (C z)
  have hbp (z : ℝ) : 0 < b z := by dsimp [b]; linarith [(hkrange z).1]
  have hCp (z : ℝ) : 0 < C z := mul_pos (by linarith [(hkrange z).1])
    (by linarith [(hkrange z).2])
  have hrp (z : ℝ) : 0 < r z := Real.sqrt_pos.2 (hCp z)
  have hrSq (z : ℝ) : r z ^ 2 = C z := Real.sq_sqrt (hCp z).le
  have hbsm : ContDiff ℝ ∞ b := (contDiff_const.mul hk).sub contDiff_const
  have hrsm : ContDiff ℝ ∞ r := (hk.mul (contDiff_const.sub hk)).sqrt (fun z => (hCp z).ne')
  obtain ⟨TD, hTf, hTi⟩ := build r b hrsm hbsm hrp hbp (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hTf' (p : E2 × ℝ) : TD p = Y (b p.2) (r p.2 • J2 p.1) p.2 := hTf p
  have hTi' (y : E3) : TD.symm y =
      (J2.symm ((r (H y))⁻¹ • (Real.sqrt 2 * (J2 (L y).1).1,
        f (b (H y)) (Real.sqrt 2 * (J2 (L y).1).2))), H y) := hTi y
  let T := TD.toHomeomorph.toOpenPartialHomeomorph
  have hTh (p : E2 × ℝ) : H (T p) = p.2 := by rw [show T p = TD p from rfl, hTf', hYh]
  have hTnorm (x : E2) (z : ℝ) (hz : z ∈ Icc (11 / 8 : ℝ) (13 / 8)) :
      ‖F0.symm (T (x, z))‖ ^ 2 = 1 + C z * (‖x‖ ^ 2 - 1) := by
    change ‖F0.symm (TD (x, z))‖ ^ 2 = _
    rw [hTf', show b z = 2 * z - 1 by dsimp [b]; rw [hke hz],
      hYn _ _ (by linarith [hz.1]), hrr, hrSq,
      show C z = z * (2 - z) by dsimp [C]; rw [hke hz]]
    ring
  have hcircleBand (z : ℝ) (hz : z ∈ Icc (11 / 8 : ℝ) (13 / 8)) :
      T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z} := by
    ext y; constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = z := ht; subst t
      refine ⟨(hS _).2 ((hband _ ((hTh _).symm ▸ hz)).1.mpr ?_), hTh _⟩
      have hn := hTnorm x z hz; rw [mem_sphere_zero_iff_norm.mp hx] at hn
      nlinarith only [hn, norm_nonneg (F0.symm (T (x, z)))]
    · rintro ⟨hyS, hyH⟩
      let x := (TD.symm y).1
      have ht : (TD.symm y).2 = z := (congrArg Prod.snd (hTi' y)).trans hyH
      have hxy : T (x, z) = y := by change TD (x, z) = y; rw [← ht]; exact TD.apply_symm_apply y
      have hn := hTnorm x z hz
      rw [hxy, (hband y (hyH.symm ▸ hz)).1.mp ((hS y).1 hyS)] at hn
      have hxs : ‖x‖ ^ 2 = 1 := sub_eq_zero.mp
        ((mul_eq_zero.mp (show C z * (‖x‖ ^ 2 - 1) = 0 by nlinarith only [hn])).resolve_left
          (hCp z).ne')
      have hx : ‖x‖ = 1 := by nlinarith only [hxs, norm_nonneg x]
      exact ⟨(x, z), ⟨mem_sphere_zero_iff_norm.mpr hx, rfl⟩, hxy⟩
  have hdisc (x : E2) (hx : ‖x‖ ≤ 1) (z : ℝ) (hz : z ∈ Icc (11 / 8 : ℝ) (13 / 8)) :
      T (x, z) ∈ F '' closedBall (0 : E3) 1 := by
    refine ⟨F.symm (T (x, z)), mem_closedBall_zero_iff.mpr ?_, F.apply_symm_apply _⟩
    apply (hband _ ((hTh _).symm ▸ hz)).2
    have hn := hTnorm x z hz
    have hxs : ‖x‖ ^ 2 ≤ 1 := by nlinarith only [hx, norm_nonneg x]
    have hm := mul_nonpos_of_nonneg_of_nonpos (hCp z).le (sub_nonpos.mpr hxs)
    nlinarith only [hn, hm, norm_nonneg (F0.symm (T (x, z)))]
  have hcircle (z : ℝ) (hz : |z - 3 / 2| < 1 / 128) :=
    hcircleBand z ⟨by linarith [(abs_lt.mp hz).1], by linarith [(abs_lt.mp hz).2]⟩
  refine ⟨k, T, hk, hkrange, hke, rfl, rfl, ?_, ?_, subset_univ _,
    TD.contDiff.contDiffOn, TD.symm.contDiff.contDiffOn, fun p _ => hTh p, ?_, hcircle, ?_⟩
  · intro p
    rw [show T p = TD p from rfl, hTf' p]
    rfl
  · intro y; rw [show T.symm y = TD.symm y from rfl, hTi']
    refine Prod.ext ?_ rfl
    apply congrArg J2.symm; ext <;> dsimp [r, C, f, b, L, H] <;> ring
  · intro y _; exact congrArg Prod.snd (hTi y)
  intro lambda hlambda hsmall
  let M := flatCapDiffeomorph P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  let cap : E3 → E3 := fun y =>
    T ((M (heightCoordinates y)).1, 3 / 2 - lambda * (M (heightCoordinates y)).2)
  let north := cap '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  have hla : lambda < 1 / 256 :=
    (le_mul_of_one_le_right hlambda.le P.one_le_heightBound).trans_lt hsmall
  obtain ⟨J, hJhem, hJbound, _, hJfiber⟩ := exists_round_profile_native_ball_model P
  obtain ⟨g, hg, _, hgm, _, hgr, hgm1, hg0⟩ :=
    exists_nonnested_reference_end_axis (-3 / 2) (1 / 2) lambda hlambda (by linarith)
  let h := g.trans (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph
  have hh (t : ℝ) : h t = -g t := rfl
  have hhm : StrictAnti h := fun _ _ hab => neg_lt_neg (hgm hab)
  have hh0 : h 0 = 3 / 2 := by rw [hh, hg0]; norm_num
  have hhm1 : h (-1) = 2 := by rw [hh, hgm1]; norm_num
  have hhr (t : ℝ) (ht : -1 / 4 ≤ t) : h t = 3 / 2 - lambda * t := by
    rw [hh, hgr t ht]; ring
  obtain ⟨kB, hkB, hkBr, hkBe⟩ := exists_saddle_end_height_clamp
    (11 / 8) (17 / 8) (1 / 8) (by norm_num) (by norm_num)
  change ∀ ⦃z : ℝ⦄, z ∈ Icc (11 / 8 : ℝ) (17 / 8) → kB z = z at hkBe
  have hkBp (z : ℝ) : 0 < kB z := by linarith [(hkBr z).1]
  let beta : ℝ → ℝ := fun t => 2 * kB (h t) - 1
  have hbetasm : ContDiff ℝ ∞ beta := (contDiff_const.mul (hkB.comp h.contDiff)).sub contDiff_const
  have hbetap (t : ℝ) : 0 < beta t := by dsimp [beta]; linarith [(hkBr (h t)).1]
  let chi : ℝ → ℝ := fun t => Real.smoothTransition (2 * t + 3 / 2)
  have hchi : ContDiff ℝ ∞ chi := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hchi0 (t : ℝ) (ht : t ≤ -3 / 4) : chi t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hquot : ContDiff ℝ ∞ (fun t : ℝ => chi t / (t + 1)) := by
    apply contDiff_iff_contDiffAt.mpr; intro t
    by_cases ht : t = -1
    · subst t; apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < -3 / 4 by norm_num)] with s hs
      rw [hchi0 s hs.le, zero_div]
    · exact hchi.contDiffAt.div (contDiffAt_id.add contDiffAt_const)
        (by intro heq; apply ht; linarith)
  let R : ℝ → ℝ := fun t => lambda + (1 / 2 - lambda) * (chi t / (t + 1))
  have hRsm : ContDiff ℝ ∞ R := contDiff_const.add (contDiff_const.mul hquot)
  have hRp (t : ℝ) : 0 < R t := by
    by_cases ht : t ≤ -3 / 4
    · simpa only [R, hchi0 t ht, zero_div, mul_zero, add_zero] using hlambda
    · have hden : 0 < t + 1 := by linarith [lt_of_not_ge ht]
      exact add_pos_of_pos_of_nonneg hlambda (mul_nonneg (by linarith)
        (div_nonneg (Real.smoothTransition.nonneg _) hden.le))
  have hRlaw (t : ℝ) : (t + 1) * R t = 2 - h t := by
    by_cases ht : t = -1
    · subst t; rw [hhm1]; norm_num
    · rw [hh, hg t]; change (t + 1) * R t =
        2 - -(-3 / 2 + lambda * t - (1 / 2 - lambda) * (1 - chi t))
      dsimp [R]; field_simp [show t + 1 ≠ 0 by intro heq; apply ht; linarith]; ring
  let bot : ℝ → ℝ := fun t => Real.sqrt (kB (h t) * R t / (1 - t)) / P.horizontal t
  let top : ℝ → ℝ := fun t => r (h t)
  have hbot (t : ℝ) (ht : t < -1 / 16) : ContDiffAt ℝ ∞ bot t := by
    exact ((((hkB.comp h.contDiff).contDiffAt.mul hRsm.contDiffAt).div
      (contDiffAt_const.sub contDiffAt_id) (by change 1 - t ≠ 0; linarith)).sqrt
        (ne_of_gt (div_pos (mul_pos (hkBp _) (hRp t))
          (by change 0 < 1 - t; linarith)))).div
          P.horizontal_smooth.contDiffAt (P.horizontal_pos t).ne'
  have hagree (t : ℝ) (ht : t ∈ Ioo (-3 / 16 : ℝ) (-1 / 16)) : bot t = top t := by
    have hht : h t ∈ Icc (11 / 8 : ℝ) (13 / 8) := by
      rw [hhr t (by linarith [ht.1])]
      constructor <;> nlinarith only [ht.1, ht.2, hlambda, hla]
    have hbval : kB (h t) = h t := hkBe ⟨hht.1, by linarith [hht.2]⟩
    have hs : 0 < 1 - t ^ 2 := by
      nlinarith only [mul_pos (show 0 < 1 - t by linarith [ht.2])
        (show 0 < 1 + t by linarith [ht.1])]
    have hbs : bot t ^ 2 = h t * (2 - h t) := by
      dsimp [bot]; rw [div_pow, Real.sq_sqrt
        (div_nonneg (mul_pos (hkBp _) (hRp t)).le (by linarith [ht.2])), hbval,
        P.horizontal_near t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩),
        inv_pow, div_inv_eq_mul, Real.sq_sqrt hs.le]
      calc
        h t * R t / (1 - t) * (1 - t ^ 2) = h t * ((t + 1) * R t) := by
          field_simp [show 1 - t ≠ 0 by linarith [ht.2]]; ring
        _ = h t * (2 - h t) := by rw [hRlaw]
    have hts : top t ^ 2 = h t * (2 - h t) := by
      change r (h t) ^ 2 = _; rw [hrSq]; dsimp [C]; rw [hke hht]
    have hbn : 0 ≤ bot t := div_nonneg (Real.sqrt_nonneg _) (P.horizontal_pos t).le
    nlinarith only [hbs, hts, hbn, (hrp (h t)).le]
  let a : ℝ → ℝ := fun t => if t < -1 / 8 then bot t else top t
  have hasm : ContDiff ℝ ∞ a := by
    apply contDiff_iff_contDiffAt.mpr; intro t
    by_cases ht : t < -1 / 8
    · apply (hbot t (by linarith)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds ht] with s hs; exact if_pos hs
    · have htt : -3 / 16 < t := by linarith [le_of_not_gt ht]
      apply (hrsm.comp h.contDiff).contDiffAt.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds htt] with s hs
      dsimp [a]; split_ifs with hss
      · exact hagree s ⟨hs, by linarith⟩
      · rfl
  have hap (t : ℝ) : 0 < a t := by
    dsimp [a]; split_ifs with ht
    · exact div_pos (Real.sqrt_pos.2 (div_pos (mul_pos (hkBp _) (hRp _))
        (by linarith))) (P.horizontal_pos _)
    · exact hrp _
  have hatop (t : ℝ) (ht : -1 / 8 ≤ t) : a t = r (h t) := if_neg (not_lt.mpr ht)
  have hheightRange (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) P.heightBound) :
      3 / 2 - lambda * P.heightBound ≤ h t ∧ h t ≤ 2 := by
    have hlo := hhm.antitone ht.2; have hhi := hhm.antitone ht.1
    rw [hhr _ (by linarith [P.one_le_heightBound])] at hlo
    rw [hhm1] at hhi; exact ⟨hlo, hhi⟩
  have hbeta (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) P.heightBound) : beta t = 2 * h t - 1 := by
    dsimp [beta]; rw [hkBe ⟨by linarith [(hheightRange t ht).1],
      by linarith [(hheightRange t ht).2]⟩]
  let rn : ℝ → ℝ := fun t => P.horizontal t * Real.sqrt (1 - t ^ 2)
  have hrn0 (t : ℝ) : 0 ≤ rn t := mul_nonneg (P.horizontal_pos t).le (Real.sqrt_nonneg _)
  have hasq (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 0) :
      a t ^ 2 * rn t ^ 2 = h t * (2 - h t) := by
    have hs : 0 ≤ 1 - t ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
        (show 0 ≤ 1 + t by linarith [ht.1])]
    have hht := hheightRange t ⟨ht.1, ht.2.trans (by linarith [P.one_le_heightBound])⟩
    by_cases hb : t < -1 / 8
    · rw [show a t = bot t from if_pos hb]
      dsimp [bot, rn]
      rw [div_pow, mul_pow, Real.sq_sqrt hs, Real.sq_sqrt
        (div_nonneg (mul_pos (hkBp _) (hRp t)).le (by linarith [ht.2])),
        hkBe ⟨by linarith [hht.1], by linarith [hht.2]⟩]
      calc
        _ = h t * ((t + 1) * R t) := by
          field_simp [(P.horizontal_pos t).ne', show 1 - t ≠ 0 by linarith [ht.2]]; ring
        _ = h t * (2 - h t) := by rw [hRlaw]
    · have hrn : rn t = 1 := by
        dsimp [rn]; rw [P.horizontal_near t (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)]
        exact inv_mul_cancel₀ (Real.sqrt_pos.2 (by
          nlinarith only [mul_pos (show 0 < 1 - t by linarith [ht.2])
            (show 0 < 1 + t by linarith [le_of_not_gt hb])])).ne'
      rw [hatop t (le_of_not_gt hb), hrn, one_pow, mul_one, hrSq]
      dsimp [C]; rw [hke ⟨by linarith [hht.1], by
        rw [hhr t (by linarith)]; nlinarith only [le_of_not_gt hb, ht.2, hlambda, hla]⟩]
  obtain ⟨Q, hQf, _hQi⟩ := build a beta hasm hbetasm hap hbetap h
  let A0 : BallNeighborhoodChart E3 E3 :=
    { chart := (J.trans Q).toHomeomorph.toOpenPartialHomeomorph
      closedBall_subset_source := subset_univ _
      smooth := (J.trans Q).contDiff.contDiffOn
      smooth_symm := (J.trans Q).symm.contDiff.contDiffOn }
  have hAf (y : E3) : A0.chart y = Y (beta (J y).2) (a (J y).2 • J2 (J y).1) (h (J y).2) := hQf _
  have hAh (y : E3) : H (A0.chart y) = h (J y).2 := by rw [hAf, hYh]
  have hQh (p : E2 × ℝ) : H (Q p) = h p.2 := by rw [hQf, hYh]
  have hE0 (y : E3) : y ∈ E0 ↔ ‖F0.symm y‖ = 1 ∧ 3 / 2 ≤ H y := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by simpa only [j0, F0.symm_apply_apply] using norm_eq_of_mem_sphere p, hp⟩
    · rintro ⟨hn, hh⟩
      exact ⟨⟨F0.symm y, mem_sphere_zero_iff_norm.mpr hn⟩,
        by change 3 / 2 ≤ H (F0 (F0.symm y)); rwa [F0.apply_symm_apply], F0.apply_symm_apply y⟩
  have hcap (p : UnitTwoSphere) (hp : 0 ≤ (heightCoordinates (p : E3)).2) :
      A0.chart (p : E3) = cap (p : E3) := by
    have hJp := (hJhem p).2 hp
    have ht : 0 ≤ (P.model p).2 := mul_nonneg (P.vertical_pos _).le hp
    have htM : (P.model p).2 ≤ P.heightBound := (abs_le.mp (P.height_bound p)).2
    have hz : h (P.model p).2 ∈ Icc (11 / 8 : ℝ) (13 / 8) := by
      rw [hhr _ (by linarith)]
      have hm := mul_le_mul_of_nonneg_left htM hlambda.le
      constructor <;> nlinarith only [hm, ht, hlambda, hsmall]
    have hbval : beta (P.model p).2 = b (h (P.model p).2) := by
      dsimp [beta, b]; rw [hkBe ⟨hz.1, by linarith [hz.2]⟩, hke hz]
    change A0.chart (p : E3) = TD ((P.model p).1, 3 / 2 - lambda * (P.model p).2)
    rw [hAf, hJp, hatop _ (by linarith), hbval, ← hhr _ (by linarith), hTf]
    rfl
  have hAlower (p : UnitTwoSphere) (hp : (heightCoordinates (p : E3)).2 ≤ 0) :
      A0.chart (p : E3) ∈ E0 := by
    let t := (heightCoordinates (p : E3)).2
    have hJp := (hJhem p).1 hp
    have ht : t ∈ Icc (-1 : ℝ) 0 :=
      ⟨by simpa only [hJp] using (hJbound p (sphere_subset_closedBall p.property)).2.1, hp⟩
    have hm : J (p : E3) ∈ (J '' sphere (0 : E3) 1) ∩ {z | z.2 = t} :=
      ⟨⟨p, p.property, rfl⟩, by change (J (p : E3)).2 = (heightCoordinates (p : E3)).2; rw [hJp]⟩
    rw [(hJfiber t ht).2.2] at hm
    obtain ⟨x, hx, hxJ⟩ := hm
    apply (hE0 _).2
    have hbval := hbeta t ⟨ht.1, ht.2.trans (by linarith [P.one_le_heightBound])⟩
    have hn : ‖F0.symm (A0.chart p)‖ ^ 2 = 1 := by
      rw [hAf, ← hxJ, hbval, hYn _ _ (by rw [← hbval]; exact hbetap t),
        hrr, mem_sphere_zero_iff_norm.mp hx, hasq t ht]
      ring
    refine ⟨by nlinarith only [hn, norm_nonneg (F0.symm (A0.chart p))], ?_⟩
    rw [hAh, ← hxJ, ← hh0]; exact hhm.antitone ht.2
  have hback (y : E3) (hy : y ∈ E0) : y ∈ A0.boundary := by
    have hy' := (hE0 y).1 hy
    have hy2 : H y ≤ 2 := by
      have hn := hF0n y; rw [hy'.1] at hn
      nlinarith only [hn, hq0 y, sq_nonneg (eta y)]
    let p := Q.symm y
    have hpy : Q p = y := Q.apply_symm_apply y
    have hpt : h p.2 = H y := (hQh p).symm.trans (congrArg H hpy)
    have ht : p.2 ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hhm.le_iff_ge.mp
      · rw [hhm1, hpt]; exact hy2
      · rw [hh0, hpt]; exact hy'.2
    have hbval := hbeta p.2 ⟨ht.1, ht.2.trans (by linarith [P.one_le_heightBound])⟩
    have hn : ‖p.1‖ = rn p.2 := by
      have hn := hYn (a p.2 • J2 p.1) (h p.2) (by rw [← hbval]; exact hbetap _)
      rw [← hbval, ← hQf, hpy, hy'.1, hrr] at hn
      have hs := hasq p.2 ht
      have heq : a p.2 ^ 2 * (‖p.1‖ ^ 2 - rn p.2 ^ 2) = 0 := by nlinarith only [hn, hs]
      have heq' := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (pow_ne_zero 2 (hap p.2).ne'))
      nlinarith only [heq', norm_nonneg p.1, hrn0 p.2]
    have hm : p ∈ (J '' sphere (0 : E3) 1) ∩ {z | z.2 = p.2} := by
      rw [(hJfiber p.2 ht).2.2]; exact ⟨p.1, mem_sphere_zero_iff_norm.mpr hn, Prod.eta p⟩
    obtain ⟨w, hw, heq⟩ := hm.1
    exact ⟨w, hw, by change Q (J w) = y; rw [heq, hpy]⟩
  have hboundary0 : A0.boundary = E0 ∪ north := by
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩
      let p : UnitTwoSphere := ⟨w, hw⟩
      by_cases hp : (heightCoordinates w).2 ≤ 0
      · exact Or.inl (hAlower p hp)
      · exact Or.inr ⟨w, ⟨mem_sphere_zero_iff_norm.mp hw, (lt_of_not_ge hp).le⟩,
          (hcap p (lt_of_not_ge hp).le).symm⟩
    · rintro (hy | ⟨w, ⟨hw, hp⟩, rfl⟩)
      · exact hback y hy
      · exact ⟨w, mem_sphere_zero_iff_norm.mpr hw, hcap ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩ hp⟩
  have imageFiber (K : Set E3) (B : Set E2) (t : ℝ)
      (hfib : (J '' K) ∩ {p | p.2 = t} = (fun x : E2 => (x, t)) '' B) :
      (A0.chart '' K) ∩ {y | H y = h t} =
        (fun x : E2 => Y (beta t) (a t • J2 x) (h t)) '' B := by
    ext y; constructor
    · rintro ⟨⟨w, hw, rfl⟩, hz⟩
      change H (A0.chart w) = h t at hz
      have ht : (J w).2 = t := h.injective (by rwa [hAh] at hz)
      have hm : J w ∈ (J '' K) ∩ {p | p.2 = t} := ⟨⟨w, hw, rfl⟩, ht⟩
      rw [hfib] at hm; obtain ⟨x, hx, heq⟩ := hm
      exact ⟨x, hx, by rw [hAf, ← heq]⟩
    · rintro ⟨x, hx, rfl⟩
      have hm : (x, t) ∈ (J '' K) ∩ {p | p.2 = t} := by rw [hfib]; exact ⟨x, hx, rfl⟩
      obtain ⟨w, hw, heq⟩ := hm.1
      exact ⟨⟨w, hw, by rw [hAf, heq]⟩, hYh _ _ _⟩
  have hfibers0 (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 / 128)) :
      A0.inside ∩ {y | H y = 3 / 2 + s} = T '' (ball (0 : E2) 1 ×ˢ ({3 / 2 + s} : Set ℝ)) ∧
      A0.closedRegion ∩ {y | H y = 3 / 2 + s} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({3 / 2 + s} : Set ℝ)) := by
    let z : ℝ := 3 / 2 + s
    let t := h.symm z
    have hht : h t = z := h.apply_symm_apply _
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hhm.le_iff_ge.mp
      · rw [hht, hhm1]; dsimp [z]; linarith [hs.2]
      · rw [hht, hh0]; dsimp [z]; linarith [hs.1]
    have htm : -1 < t := by
      apply hhm.lt_iff_gt.mp; rw [hht, hhm1]; dsimp [z]; linarith [hs.2]
    have hrad : 0 < 1 - t ^ 2 := by
      have hm := mul_pos (show 0 < 1 - t by linarith [ht.2]) (show 0 < 1 + t by linarith)
      nlinarith only [hm]
    have hrnp : 0 < rn t := mul_pos (P.horizontal_pos t) (Real.sqrt_pos.2 hrad)
    have hz : z ∈ Icc (11 / 8 : ℝ) (13 / 8) := by dsimp [z]; constructor <;> linarith [hs.1, hs.2]
    have hbval : beta t = b z := by
      rw [hbeta t ⟨ht.1, ht.2.trans (by linarith [P.one_le_heightBound])⟩, hht]
      dsimp [b]; rw [hke hz]
    have hprod : a t * rn t = r z := by
      apply (sq_eq_sq₀ (mul_pos (hap t) hrnp).le (hrp z).le).mp
      rw [mul_pow, hasq t ht, hht, hrSq]; dsimp [C]; rw [hke hz]
    have hscale (B : Set E2) :
        (fun x : E2 => Y (beta t) (a t • J2 x) z) '' ((fun w : E2 => rn t • w) '' B) =
          T '' (B ×ˢ ({z} : Set ℝ)) := by
      rw [image_image]; ext y; constructor
      · rintro ⟨x, hx, rfl⟩; refine ⟨(x, z), ⟨hx, rfl⟩, ?_⟩
        rw [show T (x, z) = TD (x, z) from rfl, hTf']
        change Y (b z) (r z • J2 x) z = Y (beta t) (a t • J2 (rn t • x)) z
        rw [map_smul, smul_smul, hprod, hbval]
      · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
        have hw' : w = z := hw; subst w; refine ⟨x, hx, ?_⟩
        rw [show T (x, z) = TD (x, z) from rfl, hTf']
        change Y (beta t) (a t • J2 (rn t • x)) z = Y (b z) (r z • J2 x) z
        rw [map_smul, smul_smul, hprod, hbval]
    have ho := imageFiber (ball (0 : E3) 1) (ball (0 : E2) (rn t)) t (hJfiber t ht).1
    have hc := imageFiber (closedBall (0 : E3) 1) (closedBall (0 : E2) (rn t)) t (hJfiber t ht).2.1
    have hball : (fun x : E2 => rn t • x) '' ball (0 : E2) 1 = ball 0 (rn t) := by
      rw [image_smul, _root_.smul_ball hrnp.ne', smul_zero, Real.norm_eq_abs,
        abs_of_pos hrnp, mul_one]
    have hclosed : (fun x : E2 => rn t • x) '' closedBall (0 : E2) 1 = closedBall 0 (rn t) := by
      rw [image_smul, smul_closedBall' hrnp.ne', smul_zero, Real.norm_eq_abs,
        abs_of_pos hrnp, mul_one]
    rw [hht, ← hball, hscale] at ho; rw [hht, ← hclosed, hscale] at hc; exact ⟨ho, hc⟩
  let v0 : E3 := L.symm (0, 1)
  have hvertical (y : E3) (t : ℝ) : q (y + t • v0) = q y ∧ H (y + t • v0) = H y + t := by
    constructor
    · dsimp [q, v0]; simp only [map_add, map_smul, L.apply_symm_apply,
        Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
    · rw [map_add, map_smul, hHs]; simp only [smul_eq_mul, mul_one]
  have hqF0 (p : E3) : q (F0 p) = p 0 ^ 2 + p 1 ^ 2 := by
    dsimp [q, F0, W]; rw [L.apply_symm_apply, ← hJ2, J2.apply_symm_apply]
    change 2 * (((nonnestedReferenceDiffeomorph 0 (fun _ => 0) contDiff_const p).1).1 ^ 2 +
      ((nonnestedReferenceDiffeomorph 0 (fun _ => 0) contDiff_const p).1).2 ^ 2) = _
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 (fun _ => 0) contDiff_const).1]
    simp only [div_pow, htwoSq]; ring
  have hFshift (p : E3) : F p = F0 p + d (q (F0 p)) • v0 := by
    apply L.injective
    rw [map_add, map_smul, show L v0 = (0, 1) from L.apply_symm_apply _, hqF0]
    have hLF : L (F p) = (J2.symm (nonnestedReferenceDiffeomorph 0 d hd p).1,
        (nonnestedReferenceDiffeomorph 0 d hd p).2) := L.apply_symm_apply _
    have hLF0 : L (F0 p) = (J2.symm (nonnestedReferenceDiffeomorph 0 (fun _ => 0)
        contDiff_const p).1, (nonnestedReferenceDiffeomorph 0 (fun _ => 0) contDiff_const p).2) :=
      L.apply_symm_apply _
    rw [hLF, hLF0,
      (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
    change (J2.symm (p 0 / Real.sqrt 2, p 1 / Real.sqrt 2),
      0 + 1 + p 2 - p 1 ^ 2 + d (p 0 ^ 2 + p 1 ^ 2)) =
      (J2.symm (p 0 / Real.sqrt 2, p 1 / Real.sqrt 2), 0 + 1 + p 2 - p 1 ^ 2 + 0) +
        d (p 0 ^ 2 + p 1 ^ 2) • (0, 1)
    apply Prod.ext <;> simp
  have hFheight (p : E3) : H (F p) = H (F0 p) + d (q (F0 p)) := by
    rw [hFshift]; exact (hvertical _ _).2
  obtain ⟨cut, hcut, _, hcuts, hcutNear, _⟩ := exists_compact_smooth_cutoff
    (K := Icc (29 / 16 : ℝ) (17 / 8)) (U := Ioo (7 / 4 : ℝ) (9 / 4))
    isCompact_Icc isOpen_Ioo (by intro z hz; constructor <;> linarith [hz.1, hz.2])
  have hcut0 (z : ℝ) (hz : z ∉ Ioo (7 / 4 : ℝ) (9 / 4)) : cut z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hz (hcuts hh))
  let X : E3 → E3 := fun y => (cut (H y) * d (q y)) • v0
  have hqsm : ContDiff ℝ ∞ q := contDiff_const.mul (L.contDiff.fst.norm_sq ℝ)
  have hX : ContDiff ℝ ∞ X := ((hcut.comp H.contDiff).mul (hd.comp hqsm)).smul contDiff_const
  let K := L.symm '' (closedBall (0 : E2) 1 ×ˢ Icc (7 / 4 : ℝ) (9 / 4))
  have hKc : IsCompact K :=
    ((isCompact_closedBall (0 : E2) 1).prod isCompact_Icc).image L.symm.continuous
  have hXZ (y : E3) (hy : y ∉ K) : X y = 0 := by
    by_cases hn : ‖(L y).1‖ ≤ 1
    · have hh : H y ∉ Ioo (7 / 4 : ℝ) (9 / 4) := by
        intro hz; apply hy; exact ⟨L y, ⟨mem_closedBall_zero_iff.mpr hn,
          by rw [hH]; exact ⟨hz.1.le, hz.2.le⟩⟩, L.symm_apply_apply y⟩
      simp only [X, hcut0 _ hh, zero_mul, zero_smul]
    · have hlarge : sigma ≤ q y := by dsimp [q]; nlinarith only [lt_of_not_ge hn, hsigmaSmall]
      simp only [X, hdZero _ hlarge, mul_zero, zero_smul]
  have hsX : HasCompactSupport X := hKc.of_isClosed_subset (isClosed_tsupport X)
    (closure_minimal (fun y hy => by by_contra hh; exact hy (hXZ y hh)) hKc.isClosed)
  obtain ⟨KK, BB, hKK, hBB⟩ := compactField_bounds X hX hsX
  let Z := boundedFlowDiffeomorph X hKK hBB hX hsX 1
  have hfix (y : E3) (hy : H y ≤ 7 / 4) : Z y = y ∧ Z.symm y = y := by
    have hz : X y = 0 := by
      simp only [X, hcut0 _ (fun hh => (not_lt_of_ge hy) hh.1), zero_mul, zero_smul]
    exact ⟨boundedFlow_eq_self X hKK hBB y hz 1, boundedFlow_eq_self X hKK hBB y hz (-1)⟩
  have hpolar (y : E3) (hy : y ∈ E0) (hsmallq : q y ≤ sigma) :
      15 / 8 ≤ H y ∧ H y ≤ 2 ∧ -1 / 512 ≤ d (q y) ∧ d (q y) ≤ 0 := by
    have hy' := (hE0 y).1 hy
    have hn := hF0n y; rw [hy'.1] at hn
    have hq : q y ≤ 1 / 16 := hsmallq.trans hsigmaSmall
    have hw0 : 0 ≤ H y - 1 + eta y ^ 2 := by linarith [hy'.2, sq_nonneg (eta y)]
    have hw : 15 / 16 ≤ H y - 1 + eta y ^ 2 :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 15 / 16) hw0).mp
        (by nlinarith only [hn, hq])
    have hq2 : q y ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := (sq_le_sq₀ (hq0 y) (by norm_num)).2 hq
    have hdb := hdBounds (q y) (hq0 y)
    exact ⟨by linarith [heta y], by nlinarith only [hn, hq0 y, sq_nonneg (eta y)],
      by linarith [hdb.1], hdb.2⟩
  have hZendPoint (p : UnitTwoSphere) (hp : 3 / 2 ≤ H (j0 p)) : Z (j0 p) = j p := by
    by_cases hq : sigma ≤ q (j0 p)
    · have hdq := hdZero _ hq
      have hz : X (j0 p) = 0 := by simp only [X, hdq, mul_zero, zero_smul]
      rw [show Z (j0 p) = j0 p from boundedFlow_eq_self X hKK hBB _ hz 1]
      change F0 p = F p; rw [hFshift, hdq, zero_smul, add_zero]
    · have hb := hpolar (j0 p) ⟨p, hp, rfl⟩ (le_of_not_ge hq)
      have htrack (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) :
          X (j0 p + t • (d (q (j0 p)) • v0)) = d (q (j0 p)) • v0 := by
        have habs : |t * d (q (j0 p))| ≤ 1 / 256 := by
          rw [abs_mul]
          have hh := mul_le_mul ((abs_lt.mpr ht).le)
            (show |d (q (j0 p))| ≤ 1 / 512 from
              abs_le.mpr ⟨by linarith [hb.2.2.1], by linarith [hb.2.2.2]⟩)
            (abs_nonneg (d (q (j0 p)))) (by norm_num : (0 : ℝ) ≤ 2)
          norm_num at hh ⊢; exact hh
        rw [smul_smul]
        have hqv := (hvertical (j0 p) (t * d (q (j0 p)))).1
        have hhv := (hvertical (j0 p) (t * d (q (j0 p)))).2
        have hc : cut (H (j0 p + (t * d (q (j0 p))) • v0)) = 1 := by
          apply subset_of_mem_nhdsSet hcutNear
          rw [hhv]; constructor <;> linarith [hb.1, hb.2.1, (abs_le.mp habs).1, (abs_le.mp habs).2]
        simp only [X, hc, hqv, one_mul]
      have heq := boundedFlow_eq_affine_on X hKK hBB (d (q (j0 p)) • v0) (j0 p)
        (by norm_num : (0 : ℝ) < 2) htrack (by norm_num : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2)
      change boundedFlow X hKK hBB (j0 p) 1 = F p
      rw [heq]; change j0 p + 1 • (d (q (j0 p)) • v0) = F p
      rw [one_smul, hFshift]
  have hZend : Z '' E0 = E := by
    ext y; constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; rw [hZendPoint p hp]
      refine ⟨p, ?_, rfl⟩
      change 3 / 2 ≤ H (F p); rw [hFheight]
      by_cases hq : sigma ≤ q (j0 p)
      · rw [hdZero _ hq, add_zero]; exact hp
      · have hb := hpolar (j0 p) ⟨p, hp, rfl⟩ (le_of_not_ge hq)
        change 3 / 2 ≤ H (j0 p) + d (q (j0 p)); linarith [hb.1, hb.2.2.1]
    · rintro ⟨p, hp, rfl⟩
      have hp0 : 3 / 2 ≤ H (j0 p) := by
        change 3 / 2 ≤ H (F p) at hp; rw [hFheight] at hp
        linarith [(hdBounds (q (F0 p)) (hq0 _)).2]
      exact ⟨j0 p, ⟨p, hp0, rfl⟩, hZendPoint p hp0⟩
  have hnorth (y : E3) (hy : y ∈ north) :
      H y ≤ 3 / 2 ∧ y ∈ F '' closedBall (0 : E3) 1 := by
    obtain ⟨w, ⟨hw, hp⟩, rfl⟩ := hy
    let p : UnitTwoSphere := ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩
    have ht : 0 ≤ (P.model p).2 := mul_nonneg (P.vertical_pos _).le hp
    have htM : (P.model p).2 ≤ P.heightBound := (abs_le.mp (P.height_bound p)).2
    have hm := mul_le_mul_of_nonneg_left htM hlambda.le
    have hx : ‖(P.model p).1‖ ≤ 1 := by
      have hh := (hJbound (p : E3) (mem_closedBall_zero_iff.mpr hw.le)).1
      rwa [(hJhem p).2 hp] at hh
    change H (T ((P.model p).1, 3 / 2 - lambda * (P.model p).2)) ≤ 3 / 2 ∧
      T ((P.model p).1, 3 / 2 - lambda * (P.model p).2) ∈ F '' closedBall (0 : E3) 1
    rw [hTh]
    exact ⟨by nlinarith only [ht, hlambda],
      hdisc _ hx _ ⟨by linarith, by nlinarith only [ht, hlambda]⟩⟩
  have hZn : Z '' north = north := by
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩; rw [(hfix w (by linarith [(hnorth w hw).1])).1]; exact hw
    · intro hy; exact ⟨y, hy, (hfix y (by linarith [(hnorth y hy).1])).1⟩
  let A := A0.mapDiffeomorph Z
  have hboundary : A.boundary = E ∪ north := by
    rw [BallNeighborhoodChart.mapDiffeomorph_boundary, hboundary0, image_union, hZend, hZn]
  let B : BallNeighborhoodChart E3 E3 :=
    { chart := F.toHomeomorph.toOpenPartialHomeomorph, closedBall_subset_source := subset_univ _
      smooth := F.contDiff.contDiffOn, smooth_symm := F.symm.contDiff.contDiffOn }
  have hcontained : A.closedRegion ⊆ F '' closedBall (0 : E3) 1 := by
    apply saddle_ball_closedRegion_subset_of_boundary_subset B A
    rw [hboundary]; rintro y (hy | hy)
    · obtain ⟨p, _, rfl⟩ := hy; exact ⟨p, sphere_subset_closedBall p.property, rfl⟩
    · exact (hnorth y hy).2
  have hAheight : A.closedRegion ⊆ {y | 3 / 2 - lambda * P.heightBound ≤ H y} := by
    rintro y ⟨w, hw, rfl⟩
    change 3 / 2 - lambda * P.heightBound ≤ H (Z (A0.chart w))
    have hlo : 3 / 2 - lambda * P.heightBound ≤ H (A0.chart w) := by
      rw [hAh]; exact (hheightRange _ (hJbound w hw).2).1
    by_cases hz : H (Z (A0.chart w)) ≤ 7 / 4
    · have heq : A0.chart w = Z (A0.chart w) :=
        (Z.symm_apply_apply _).symm.trans (hfix _ hz).2
      rwa [← heq]
    · have hM : 0 < lambda * P.heightBound := mul_pos hlambda (by linarith [P.one_le_heightBound])
      linarith [lt_of_not_ge hz]
  have hslice (D : Set E3) (z : ℝ) (hz : z ≤ 7 / 4) :
      (Z '' D) ∩ {y | H y = z} = D ∩ {y | H y = z} := by
    ext y; constructor
    · rintro ⟨⟨w, hw, rfl⟩, hh⟩
      have heq : w = Z w := (Z.symm_apply_apply w).symm.trans (hfix _ (hh.symm ▸ hz)).2
      exact ⟨heq ▸ hw, hh⟩
    · rintro ⟨hy, hh⟩; exact ⟨⟨y, hy, (hfix y (hh.symm ▸ hz)).1⟩, hh⟩
  refine ⟨A, hboundary, hcontained, hAheight, ?_, ?_⟩
  · intro s hs
    rw [BallNeighborhoodChart.mapDiffeomorph_inside,
      BallNeighborhoodChart.mapDiffeomorph_closedRegion,
      hslice _ _ (by linarith [hs.2]), hslice _ _ (by linarith [hs.2])]
    exact hfibers0 s hs
  · intro p hp
    by_cases hp0 : 0 ≤ (heightCoordinates (p : E3)).2
    · rw [hboundary]; exact Or.inr ⟨p, ⟨norm_eq_of_mem_sphere p, hp0⟩, rfl⟩
    · have hpneg := lt_of_not_ge hp0
      have hmodel : P.model p = ((circleDirection (heightCoordinates (p : E3)).1 : E2),
          (heightCoordinates (p : E3)).2) := surgeryCapModel_cylinder P.horizontal P.vertical
        P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        P.horizontal_near P.vertical_far p (abs_le.mpr ⟨by linarith, by linarith⟩)
      let z := 3 / 2 - lambda * (heightCoordinates (p : E3)).2
      have hz : |z - 3 / 2| < 1 / 128 := by
        apply abs_lt.mpr
        have hlo := mul_lt_mul_of_pos_left hp hlambda
        have hhi := mul_neg_of_pos_of_neg hlambda hpneg
        change -(1 / 128) < 3 / 2 - lambda * (heightCoordinates (p : E3)).2 - 3 / 2 ∧
          3 / 2 - lambda * (heightCoordinates (p : E3)).2 - 3 / 2 < 1 / 128
        constructor <;> nlinarith only [hlo, hhi, hla]
      have hc : cap p ∈ T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
        refine ⟨((circleDirection (heightCoordinates (p : E3)).1 : E2), z),
          ⟨(circleDirection (heightCoordinates (p : E3)).1).property, rfl⟩, ?_⟩
        change T _ = T ((P.model p).1, 3 / 2 - lambda * (P.model p).2); rw [hmodel]
      rw [hcircle z hz] at hc
      rw [hboundary]; left
      obtain ⟨p', hp'⟩ := hc.1
      refine ⟨p', ?_, hp'⟩
      change 3 / 2 ≤ H (j p'); rw [hp', hc.2]
      change 3 / 2 ≤ 3 / 2 - lambda * (heightCoordinates (p : E3)).2
      nlinarith only [hlambda, hpneg]

end PoincareConjecture.M25.Topology3D
