import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Transition

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_upper_halfspace_graft
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hheight : ∀ p, F p 2 = p 2) {ε : Real} (hε : 0 < ε)
    (hcentral : ∀ p : E3, |p 2| < ε → F p = p) :
    ∃ E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p, E p 2 = p 2) ∧
      (∀ p, p 2 < ε → E p = p) ∧
      ∀ p, 0 ≤ p 2 → E p = F p := by
  have hih (p : E3) : F.symm p 2 = p 2 := by
    have he := hheight (F.symm p)
    rw [F.apply_symm_apply] at he
    exact he.symm
  have hic (p : E3) (hp : |p 2| < ε) : F.symm p = p := by
    apply F.injective
    change F (F.symm p) = F p
    rw [F.apply_symm_apply, hcentral p hp]
  let graft (D : E3 → E3) (p : E3) : E3 := if 0 ≤ p 2 then D p else p
  have hlow (D : E3 → E3) (hD : ∀ p : E3, |p 2| < ε → D p = p)
      (p : E3) (hp : p 2 < ε) : graft D p = p := by
    dsimp [graft]
    split_ifs with h
    · exact hD p (by rwa [abs_of_nonneg h])
    · rfl
  have hsmooth (D : E3 → E3) (hD : ContDiff Real ∞ D)
      (hDc : ∀ p : E3, |p 2| < ε → D p = p) : ContDiff Real ∞ (graft D) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p 2 < ε
    · apply contDiffAt_id.congr_of_eventuallyEq
      filter_upwards [((isOpen_lt
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).continuous
        (continuous_const : Continuous (fun _ : E3 => ε))).mem_nhds hp)] with q hq
      exact hlow D hDc q hq
    · apply hD.contDiffAt.congr_of_eventuallyEq
      have hp0 : 0 < p 2 := hε.trans_le (le_of_not_gt hp)
      filter_upwards [((isOpen_lt (continuous_const : Continuous (fun _ : E3 => (0 : Real)))
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).continuous).mem_nhds hp0)] with q hq
      exact if_pos hq.le
  have hleft (p : E3) : graft F.symm (graft F p) = p := by
    by_cases hp : 0 ≤ p 2
    · simp only [graft, if_pos hp, hheight, F.symm_apply_apply]
    · simp only [graft, if_neg hp]
  have hright (p : E3) : graft F (graft F.symm p) = p := by
    by_cases hp : 0 ≤ p 2
    · simp only [graft, if_pos hp, hih, F.apply_symm_apply]
    · simp only [graft, if_neg hp]
  let E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toFun := graft F
    invFun := graft F.symm
    left_inv := hleft
    right_inv := hright
    contMDiff_toFun := (hsmooth F F.contDiff hcentral).contMDiff
    contMDiff_invFun := (hsmooth F.symm F.symm.contDiff hic).contMDiff }
  refine ⟨E, ?_, hlow F hcentral, ?_⟩
  · intro p
    change (if 0 ≤ p 2 then F p else p) 2 = p 2
    split_ifs <;> first | exact hheight p | rfl
  · intro p hp
    exact if_pos hp

def horizontalScaleLift (r : Real → Real) (hr : ContDiff Real ∞ r)
    (hpos : ∀ t, 0 < r t) : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := vector (r (p 2) * p 0) (r (p 2) * p 1) (p 2)
  invFun p := vector ((r (p 2))⁻¹ * p 0) ((r (p 2))⁻¹ * p 1) (p 2)
  left_inv p := by
    ext i
    fin_cases i
    · change (r (p 2))⁻¹ * (r (p 2) * p 0) = p 0
      rw [← mul_assoc, inv_mul_cancel₀ (hpos (p 2)).ne', one_mul]
    · change (r (p 2))⁻¹ * (r (p 2) * p 1) = p 1
      rw [← mul_assoc, inv_mul_cancel₀ (hpos (p 2)).ne', one_mul]
    · rfl
  right_inv p := by
    ext i
    fin_cases i
    · change r (p 2) * ((r (p 2))⁻¹ * p 0) = p 0
      rw [← mul_assoc, mul_inv_cancel₀ (hpos (p 2)).ne', one_mul]
    · change r (p 2) * ((r (p 2))⁻¹ * p 1) = p 1
      rw [← mul_assoc, mul_inv_cancel₀ (hpos (p 2)).ne', one_mul]
    · rfl
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (hr.comp (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff).mul
        (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (hr.comp (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff).mul
        (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    have hi : ContDiff Real ∞ (fun p : E3 => (r (p 2))⁻¹) :=
      (hr.comp (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff).inv
        (fun p => (hpos (p 2)).ne')
    fin_cases i
    · exact hi.mul (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact hi.mul (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff

@[simp] theorem horizontalScaleLift_height (r : Real → Real) (hr : ContDiff Real ∞ r)
    (hpos : ∀ t, 0 < r t) (p : E3) : horizontalScaleLift r hr hpos p 2 = p 2 := rfl

theorem exists_relative_cylindrical_cap_graft
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hGheight : ∀ p, G p 2 = p 2)
    {σ : Real} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hG : ∀ t, |t| ≤ σ → ∀ q : E2,
      G (tangentPlanarLatitude t q) = sliceAtHeight t (A q))
    (r : Real → Real) (hr : ContDiff Real ∞ r) (hpos : ∀ t, 0 < r t)
    (hrlocal : ∀ t, |t| ≤ σ → r t = (Real.sqrt (1 - t ^ 2))⁻¹) :
    ∃ (η : Real) (E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ (∀ p : E3, p 2 ≤ η → E p = p) ∧
      (∀ p, E p 2 = p 2) ∧
      E '' (planarCapLift A '' (horizontalScaleLift r hr hpos ''
        (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}))) =
          G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}) := by
  let B := horizontalScaleLift r hr hpos
  let T := B.trans (planarCapLift A)
  have hTh (p : E3) : T p 2 = p 2 := by
    change planarCapLift A (B p) 2 = p 2
    rw [planarCapLift_height, horizontalScaleLift_height]
  have hTi (p : E3) : T.symm p 2 = p 2 := by
    have he := hTh (T.symm p)
    rw [T.apply_symm_apply] at he
    exact he.symm
  have hGT (p : E3) (hp : |p 2| < σ) : G p = T p := by
    have hpI : p 2 ∈ Ioo (-1 : Real) 1 := abs_lt.mp (hp.trans hσ1)
    have h := hG (p 2) hp.le ((Real.sqrt (1 - p 2 ^ 2))⁻¹ • horizontal p)
    rw [tangentPlanarLatitude_normalized_horizontal p hpI] at h
    change G p = planarCapLift A (B p)
    rw [planarCapLift_apply, horizontalScaleLift_height]
    have hB : horizontal (B p) = (Real.sqrt (1 - p 2 ^ 2))⁻¹ • horizontal p := by
      ext i
      fin_cases i <;> change r (p 2) * _ = _ <;> rw [hrlocal (p 2) hp.le] <;> rfl
    rw [hB]
    exact h
  let F := T.symm.trans G
  have hFh (p : E3) : F p 2 = p 2 := (hGheight (T.symm p)).trans (hTi p)
  have hFc (p : E3) (hp : |p 2| < σ) : F p = p := by
    change G (T.symm p) = p
    rw [hGT (T.symm p) (by rw [hTi]; exact hp), T.apply_symm_apply]
  obtain ⟨E, hEh, hElow, hEupper⟩ := exists_upper_halfspace_graft F hFh hσ hFc
  refine ⟨σ / 2, E, half_pos hσ, fun p hp => hElow p (by linarith), hEh, ?_⟩
  rw [image_image, image_image]
  apply image_congr
  intro p hp
  change E (T p) = G p
  rw [hEupper (T p) (by rw [hTh]; exact hp.2)]
  change G (T.symm (T p)) = G p
  rw [T.symm_apply_apply]

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
