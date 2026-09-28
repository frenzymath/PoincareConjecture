import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MorseRadialChart
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_nestedReference_buffered_morse_chart
    (w : ℝ) (hw_lower : 1 / 2 < w) (hw_upper : w < 3 / 4)
    (m : OpenPartialHomeomorph E2 (ℝ × ℝ))
    (hm_point : (!₂[-Real.sqrt (1 - w ^ 2), 0] : E2) ∈ m.source)
    (hm_source : m.source ⊆ Metric.ball (0 : E2) 1)
    (hm_zero : m (!₂[-Real.sqrt (1 - w ^ 2), 0] : E2) = 0)
    (hm : ContDiffOn ℝ ∞ m m.source)
    (hmi : ContDiffOn ℝ ∞ m.symm m.target)
    (hm_height : ∀ v ∈ m.source,
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 =
        1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32 -
          (m v).1 ^ 2 + (m v).2 ^ 2) :
    let vstar : E2 := !₂[-Real.sqrt (1 - w ^ 2), 0]
    let pstar : UnitTwoSphere := northSpherePoint ((1 + w)⁻¹ • vstar)
    let kappa : ℝ := 1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32
    ∃ (R b : ℝ)
      (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
      (P : OpenPartialHomeomorph (ℝ × ℝ) E2),
      0 < R ∧ 0 < b ∧ b ≤ 1 / 64 ∧
      4 * R ^ 2 < b ∧ 16 * b < kappa - 17 / 16 ∧
      heightCoordinates (pstar : E3) = (vstar, w) ∧
      e.source = {q : UnitTwoSphere |
        0 < (heightCoordinates (q : E3)).2 ∧
          (heightCoordinates (q : E3)).1 ∈ m.source} ∧
      e.target = m.target ∧
      (∀ q : UnitTwoSphere, e q = m (heightCoordinates (q : E3)).1) ∧
      (∀ s ∈ e.target, e.symm s = northSpherePoint
        ((1 + Real.sqrt (1 - ‖m.symm s‖ ^ 2))⁻¹ • m.symm s)) ∧
      pstar ∈ e.source ∧ e pstar = 0 ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target ∧
      (∀ d : ℝ, ∀ q ∈ e.source,
        (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
          kappa + d - (e q).1 ^ 2 + (e q).2 ^ 2) ∧
      (∀ d : ℝ, mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun q : UnitTwoSphere =>
          (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2)
        pstar = 0) ∧
      P.source = {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ∧
      P.target = m.symm ''
        {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ∧
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ (2 * R) ^ 2} ⊆ e.target ∧
      (∀ s : ℝ × ℝ, P s = m.symm s) ∧
      (∀ v ∈ P.target, P.symm v = m v) ∧
      P.target ⊆ m.source ∧ P 0 = vstar ∧
      ContDiffOn ℝ ∞ P P.source ∧
      ContDiffOn ℝ ∞ P.symm P.target ∧
      ∀ c : ℝ, ∃ A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3,
        A.source =
          {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ×ˢ
            Set.Ioo (c - 8 * b) (c + 8 * b) ∧
        A.target = heightCoordinates.symm ''
          (P.target ×ˢ Set.Ioo (c - 8 * b) (c + 8 * b)) ∧
        ContDiffOn ℝ ∞ A A.source ∧
        ContDiffOn ℝ ∞ A.symm A.target ∧
        A (0, c) = nestedReferenceDiffeomorph (c - kappa) (pstar : E3) ∧
        ({s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2} ×ˢ
          Set.Icc (c - 4 * b) (c + 4 * b)) ⊆ A.source ∧
        (∀ s ∈ P.source, (s, c - s.1 ^ 2 + s.2 ^ 2) ∈ A.source) ∧
        (∀ y ∈ A.target, A.symm y =
          (P.symm (heightCoordinates y).1, (heightCoordinates y).2)) ∧
        ∀ q ∈ A.source,
          A q = heightCoordinates.symm (P q.1, q.2) ∧
          (heightCoordinates (A q)).2 = q.2 ∧
          w / 2 < (heightCoordinates
            ((nestedReferenceDiffeomorph (c - kappa)).symm (A q))).2 ∧
          (A q ∈ (nestedReferenceBallChart (c - kappa)).boundary ↔
            q.2 = c - q.1.1 ^ 2 + q.1.2 ^ 2) ∧
          (A q ∈ (nestedReferenceBallChart (c - kappa)).closedRegion ↔
            q.2 ≤ c - q.1.1 ^ 2 + q.1.2 ^ 2) ∧
          (A q ∈ (nestedReferenceBallChart (c - kappa)).inside ↔
            q.2 < c - q.1.1 ^ 2 + q.1.2 ^ 2) ∧
          (A q ∉ (nestedReferenceBallChart (c - kappa)).closedRegion ↔
            c - q.1.1 ^ 2 + q.1.2 ^ 2 < q.2) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let vstar : E2 := !₂[-Real.sqrt (1 - w ^ 2), 0]
  let pstar : UnitTwoSphere := northSpherePoint ((1 + w)⁻¹ • vstar)
  let kappa : ℝ := 1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32
  change ∃ (R b : ℝ) (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2), _
  have hw0 : 0 < w := by linarith
  have hw1 : w < 1 := by linarith
  have hwSq : w ^ 2 < 1 := by nlinarith
  have haSq : (Real.sqrt (1 - w ^ 2)) ^ 2 = 1 - w ^ 2 :=
    Real.sq_sqrt (sub_pos.mpr hwSq).le
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hstarSq : ‖vstar‖ ^ 2 = 1 - w ^ 2 := by
    rw [hNorm]
    change (-Real.sqrt (1 - w ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
    nlinarith only [haSq]
  have hstarNorm : ‖vstar‖ < 1 := mem_ball_zero_iff.mp (hm_source hm_point)
  have hstarSqrt : Real.sqrt (1 - ‖vstar‖ ^ 2) = w := by
    rw [hstarSq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hw0]
  have h0m : (0 : ℝ × ℝ) ∈ m.target := hm_zero ▸ m.map_source hm_point
  have hm0 : m.symm 0 = vstar := by
    calc
      m.symm 0 = m.symm (m vstar) := congrArg m.symm hm_zero.symm
      _ = vstar := m.left_inv hm_point
  have hkappa : 17 / 16 < kappa := by
    have ha1 : Real.sqrt (1 - w ^ 2) < 1 := by
      nlinarith only [haSq, pow_pos hw0 2, Real.sqrt_nonneg (1 - w ^ 2)]
    have hprod : 0 < (3 / 4 - w) * (w - 1 / 4) :=
      mul_pos (sub_pos.mpr hw_upper) (by linarith)
    dsimp only [kappa]
    nlinarith only [hprod, ha1]

  let up : E2 → UnitTwoSphere := fun v => -southSpherePoint (-v)
  have hupFormula (v : E2) : up v = northSpherePoint
      ((1 + Real.sqrt (1 - ‖v‖ ^ 2))⁻¹ • v) := by
    simp only [up, southSpherePoint, norm_neg, smul_neg, neg_neg]
  have hupCoordinates (v : E2) (hv : ‖v‖ < 1) :
      heightCoordinates (up v : E3) = (v, Real.sqrt (1 - ‖v‖ ^ 2)) := by
    change heightCoordinates ((-southSpherePoint (-v) : UnitTwoSphere) : E3) = _
    rw [coe_neg_sphere, map_neg,
      southSpherePoint_coordinates (-v) (by simpa only [norm_neg] using hv), norm_neg]
    change (-(-v), -(-Real.sqrt (1 - ‖v‖ ^ 2))) =
      (v, Real.sqrt (1 - ‖v‖ ^ 2))
    simp only [neg_neg]
  have hupSmooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ up (ball (0 : E2) 1) := by
    have hneg : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞
        (fun v : E2 => -v) (ball (0 : E2) 1) :=
      contDiff_id.neg.contMDiff.contMDiffOn
    exact contMDiff_neg_sphere.comp_contMDiffOn
      (southSpherePoint_contMDiffOn.comp hneg (fun v hv => by
        change -v ∈ ball (0 : E2) 1
        simpa only [mem_ball_zero_iff, norm_neg] using hv))
  have hupInverse (q : UnitTwoSphere)
      (hq : 0 < (heightCoordinates (q : E3)).2) :
      ‖(heightCoordinates (q : E3)).1‖ < 1 ∧
        up (heightCoordinates (q : E3)).1 = q := by
    have hs := sphere_height_coordinates_sq q
    have hx : ‖(heightCoordinates (q : E3)).1‖ < 1 := by
      nlinarith [norm_nonneg (heightCoordinates (q : E3)).1, pow_pos hq 2]
    refine ⟨hx, ?_⟩
    apply Subtype.ext
    apply heightCoordinates.injective
    rw [hupCoordinates _ hx]
    have hr : 1 - ‖(heightCoordinates (q : E3)).1‖ ^ 2 =
        (heightCoordinates (q : E3)).2 ^ 2 := by linarith only [hs]
    rw [hr, Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hprojection : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞
      (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).1) :=
    contDiff_fst.contMDiff.comp
      (heightCoordinates.contDiff.contMDiff.comp contMDiff_coe_sphere)
  let H : OpenPartialHomeomorph UnitTwoSphere E2 := {
    toFun := fun q => (heightCoordinates (q : E3)).1
    invFun := up
    source := {q | 0 < (heightCoordinates (q : E3)).2}
    target := ball 0 1
    map_source' := fun q hq => mem_ball_zero_iff.mpr (hupInverse q hq).1
    map_target' := by
      intro v hv
      change 0 < (heightCoordinates (up v : E3)).2
      rw [hupCoordinates v (mem_ball_zero_iff.mp hv)]
      apply Real.sqrt_pos.mpr
      nlinarith [mem_ball_zero_iff.mp hv, norm_nonneg v]
    left_inv' := fun q hq => (hupInverse q hq).2
    right_inv' := by
      intro v hv
      exact congrArg Prod.fst (hupCoordinates v (mem_ball_zero_iff.mp hv))
    open_source := isOpen_lt continuous_const
      (heightCoordinates.continuous.comp continuous_subtype_val).snd
    open_target := isOpen_ball
    continuousOn_toFun := hprojection.continuous.continuousOn
    continuousOn_invFun := hupSmooth.continuousOn }
  let e := H.trans m
  have hes : e.source = {q : UnitTwoSphere |
      0 < (heightCoordinates (q : E3)).2 ∧
        (heightCoordinates (q : E3)).1 ∈ m.source} := rfl
  have het : e.target = m.target := by
    apply Subset.antisymm inter_subset_left
    intro s hs
    exact ⟨hs, hm_source (m.map_target hs)⟩
  have hef (q : UnitTwoSphere) : e q = m (heightCoordinates (q : E3)).1 := rfl
  have hei (s : ℝ × ℝ) (_hs : s ∈ e.target) : e.symm s = northSpherePoint
      ((1 + Real.sqrt (1 - ‖m.symm s‖ ^ 2))⁻¹ • m.symm s) :=
    hupFormula (m.symm s)
  have heSmooth : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source :=
    hm.contMDiffOn.comp hprojection.contMDiffOn (fun _ hq => hq.2)
  have heInverseSmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target :=
    hupSmooth.comp (hmi.contMDiffOn.mono inter_subset_left) (fun _ hs => hs.2)
  have hpup : pstar = up vstar := by
    rw [hupFormula, hstarSqrt]
  have hpCoordinates : heightCoordinates (pstar : E3) = (vstar, w) := by
    rw [hpup, hupCoordinates vstar hstarNorm, hstarSqrt]
  have hpe : pstar ∈ e.source := by
    change 0 < (heightCoordinates (pstar : E3)).2 ∧
      (heightCoordinates (pstar : E3)).1 ∈ m.source
    rw [hpCoordinates]
    exact ⟨hw0, hm_point⟩
  have heZero : e pstar = 0 := by
    rw [hef, hpCoordinates]
    exact hm_zero
  have hShear (d : ℝ) (y : E3) :
      heightCoordinates (nestedReferenceDiffeomorph d y) =
        ((heightCoordinates y).1, (heightCoordinates y).2 +
          ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).1 0 / 32 + d) := by
    rw [(nestedReferenceDiffeomorph_apply_symm d).1 y]
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · change y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d =
        y 2 + ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).1 0 / 32 + d
      rw [hNorm]
      change y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d =
        y 2 + ((y 0) ^ 2 + (y 1) ^ 2) + y 0 / 32 + d
      ring
  have heHeight (d : ℝ) (q : UnitTwoSphere) (hq : q ∈ e.source) :
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        kappa + d - (e q).1 ^ 2 + (e q).2 ^ 2 := by
    change 0 < (heightCoordinates (q : E3)).2 ∧
      (heightCoordinates (q : E3)).1 ∈ m.source at hq
    have hs := sphere_height_coordinates_sq q
    have hsqrt : Real.sqrt (1 - ‖(heightCoordinates (q : E3)).1‖ ^ 2) =
        (heightCoordinates (q : E3)).2 := by
      rw [show 1 - ‖(heightCoordinates (q : E3)).1‖ ^ 2 =
        (heightCoordinates (q : E3)).2 ^ 2 by linarith only [hs],
        Real.sqrt_sq_eq_abs, abs_of_pos hq.1]
    have hh := hm_height (heightCoordinates (q : E3)).1 hq.2
    rw [hsqrt] at hh
    rw [hShear, hef]
    change (heightCoordinates (q : E3)).2 + ‖(heightCoordinates (q : E3)).1‖ ^ 2 +
      (heightCoordinates (q : E3)).1 0 / 32 + d = _
    dsimp only [kappa]
    linarith only [hh]
  have hcritical (d : ℝ) : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun q : UnitTwoSphere =>
        (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2) pstar = 0 := by
    let G : ℝ × ℝ → ℝ := fun s => kappa + d - s.1 ^ 2 + s.2 ^ 2
    have hx : HasFDerivAt (fun s : ℝ × ℝ => s.1 ^ 2)
        (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0 : ℝ × ℝ) := by
      simpa using ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
        (x := (0 : ℝ × ℝ))).pow 2
    have hy : HasFDerivAt (fun s : ℝ × ℝ => s.2 ^ 2)
        (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0 : ℝ × ℝ) := by
      simpa using ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
        (x := (0 : ℝ × ℝ))).pow 2
    have hG : HasFDerivAt G (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0 : ℝ × ℝ) := by
      convert! ((hasFDerivAt_const (kappa + d) (0 : ℝ × ℝ)).sub hx).add hy using 1
      simp only [sub_zero, add_zero]
    have heD := (heSmooth.contMDiffAt (e.open_source.mem_nhds hpe)).mdifferentiableAt
      (by simp)
    have hGD : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) G (e pstar) := by
      rw [heZero]
      exact hG.hasMFDerivAt.mdifferentiableAt
    have hlocal : (fun q : UnitTwoSphere =>
        (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2) =ᶠ[𝓝 pstar]
          G ∘ e := by
      filter_upwards [e.open_source.mem_nhds hpe] with q hq
      exact heHeight d q hq
    rw [hlocal.mfderiv_eq, mfderiv_comp pstar hGD heD, heZero,
      mfderiv_eq_fderiv, hG.fderiv]
    exact ContinuousLinearMap.zero_comp _

  let T : Set ((ℝ × ℝ) × ℝ) := m.target ×ˢ univ
  let residual : ((ℝ × ℝ) × ℝ) → ℝ := fun q =>
    q.2 - ‖m.symm q.1‖ ^ 2 - (m.symm q.1) 0 / 32
  have harg : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => m.symm q.1) T :=
    m.symm.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq.1)
  have hresidual : ContinuousOn residual T :=
    (continuous_snd.continuousOn.sub ((continuous_norm.comp_continuousOn harg).pow 2)).sub
      (((EuclideanSpace.proj 0).continuous.comp_continuousOn harg).div_const 32)
  let W : Set ((ℝ × ℝ) × ℝ) := T ∩ residual ⁻¹' Ioi (w / 2)
  have hW : IsOpen W := hresidual.isOpen_inter_preimage
    (m.open_target.prod isOpen_univ) isOpen_Ioi
  have hresidual0 : residual (0, kappa) = w := by
    dsimp only [residual]
    rw [hm0, hstarSq]
    change kappa - (1 - w ^ 2) - (-Real.sqrt (1 - w ^ 2)) / 32 = w
    dsimp only [kappa]
    ring
  have h0W : ((0 : ℝ × ℝ), kappa) ∈ W := by
    refine ⟨⟨h0m, mem_univ _⟩, ?_⟩
    change w / 2 < residual (0, kappa)
    rw [hresidual0]
    linarith
  obtain ⟨eta, heta, hetaW⟩ := Metric.isOpen_iff.mp hW (0, kappa) h0W
  let b : ℝ := min (eta / 32) (min ((kappa - 17 / 16) / 32) (1 / 64))
  have hb : 0 < b := by dsimp only [b]; positivity
  have hbEta : b ≤ eta / 32 := min_le_left _ _
  have hbGap : b ≤ (kappa - 17 / 16) / 32 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hb64 : b ≤ 1 / 64 := (min_le_right _ _).trans (min_le_right _ _)
  have hbGapStrict : 16 * b < kappa - 17 / 16 := by linarith only [hbGap, hkappa]
  let R : ℝ := min (eta / 8) (Real.sqrt b / 4)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hREta : R ≤ eta / 8 := min_le_left _ _
  have hRSqrt : R ≤ Real.sqrt b / 4 := min_le_right _ _
  have hRsmall : R ^ 2 ≤ b / 16 := by
    have h := (sq_le_sq₀ hR.le (show (0 : ℝ) ≤ Real.sqrt b / 4 by positivity)).mpr hRSqrt
    simpa only [div_pow, Real.sq_sqrt hb.le, show (4 : ℝ) ^ 2 = 16 by norm_num] using h
  have hRheight : 4 * R ^ 2 < b := by linarith only [hRsmall, hb]
  have hbuffer (s : ℝ × ℝ) (z : ℝ)
      (hs : s.1 ^ 2 + s.2 ^ 2 ≤ (2 * R) ^ 2) (hz : |z - kappa| ≤ 8 * b) :
      (s, z) ∈ W := by
    apply hetaW
    have hsnorm : ‖s‖ ≤ 2 * R := by
      rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
      constructor
      · apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * R)).mp
        rw [sq_abs]
        nlinarith only [hs, sq_nonneg s.2]
      · apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * R)).mp
        rw [sq_abs]
        nlinarith only [hs, sq_nonneg s.1]
    change max (dist s 0) (dist z kappa) < eta
    rw [dist_zero_right, Real.dist_eq, max_lt_iff]
    exact ⟨hsnorm.trans_lt (by linarith only [hREta, heta]),
      hz.trans_lt (by linarith only [hbEta, heta])⟩
  have hclosedTarget : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ (2 * R) ^ 2} ⊆ m.target := by
    intro s hs
    exact (hbuffer s kappa hs (by rw [sub_self, abs_zero]; positivity)).1.1
  let D : Set (ℝ × ℝ) := {s | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2}
  have hD : IsOpen D := (morseRadialDisc_geometry (2 * R) (by positivity)).1
  have hDtarget : D ⊆ m.target := fun s hs => hclosedTarget
    (show s.1 ^ 2 + s.2 ^ 2 ≤ (2 * R) ^ 2 from hs.le)
  let P := m.symm.restrOpen D hD
  have hPsource : P.source = D := inter_eq_right.mpr hDtarget
  have hPtarget : P.target = m.symm '' D := by
    rw [← P.image_source_eq_target, hPsource]
    rfl
  have hPsubset : P.target ⊆ m.source := inter_subset_left
  have hPzero : P 0 = vstar := hm0
  have hPs : ContDiffOn ℝ ∞ P P.source := hmi.mono inter_subset_left
  have hPi : ContDiffOn ℝ ∞ P.symm P.target := hm.mono inter_subset_left
  have hInverseHeight (d : ℝ) (v : E2) (z : ℝ) :
      (heightCoordinates ((nestedReferenceDiffeomorph d).symm
        (heightCoordinates.symm (v, z)))).2 = z - ‖v‖ ^ 2 - v 0 / 32 - d := by
    rw [(nestedReferenceDiffeomorph_apply_symm d).2 (heightCoordinates.symm (v, z)),
      heightCoordinates_snd_apply, heightCoordinates_symm_apply]
    change z - (v 0) ^ 2 - (v 1) ^ 2 - v 0 / 32 - d = _
    rw [hNorm]
    ring
  have hRegions (d : ℝ) (v : E2) (z : ℝ) :
      (heightCoordinates.symm (v, z) ∈ (nestedReferenceBallChart d).inside ↔
        ‖v‖ ^ 2 + (z - ‖v‖ ^ 2 - v 0 / 32 - d) ^ 2 < 1) ∧
      (heightCoordinates.symm (v, z) ∈ (nestedReferenceBallChart d).closedRegion ↔
        ‖v‖ ^ 2 + (z - ‖v‖ ^ 2 - v 0 / 32 - d) ^ 2 ≤ 1) ∧
      (heightCoordinates.symm (v, z) ∈ (nestedReferenceBallChart d).boundary ↔
        ‖v‖ ^ 2 + (z - ‖v‖ ^ 2 - v 0 / 32 - d) ^ 2 = 1) := by
    let y := heightCoordinates.symm (v, z)
    have hy0 : y 0 = v 0 := by dsimp only [y]; rw [heightCoordinates_symm_apply]; rfl
    have hy1 : y 1 = v 1 := by dsimp only [y]; rw [heightCoordinates_symm_apply]; rfl
    have hy2 : y 2 = z := by dsimp only [y]; rw [heightCoordinates_symm_apply]; rfl
    have hsum : (y 0) ^ 2 + (y 1) ^ 2 = ‖v‖ ^ 2 := by rw [hy0, hy1, hNorm]
    have hres : y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d =
        z - ‖v‖ ^ 2 - v 0 / 32 - d := by
      rw [hy0, hy1, hy2, hNorm]
      ring
    simpa only [hsum, hres] using (nestedReferenceBallChart_regions d).2.2.2 y
  refine ⟨R, b, e, P, hR, hb, hb64, hRheight, hbGapStrict, hpCoordinates,
    hes, het, hef, hei, hpe, heZero, heSmooth, heInverseSmooth, heHeight,
    hcritical, hPsource, hPtarget, ?_, fun _ => rfl, fun _ _ => rfl,
    hPsubset, hPzero, hPs, hPi, ?_⟩
  · rw [het]
    exact hclosedTarget
  · intro c
    let I : Set ℝ := Ioo (c - 8 * b) (c + 8 * b)
    let C := P.prod (OpenPartialHomeomorph.ofSet I isOpen_Ioo)
    let A := C.trans heightCoordinates.symm.toHomeomorph.toOpenPartialHomeomorph
    have hAsource : A.source = D ×ˢ I := by
      change (P.source ×ˢ I) ∩ C ⁻¹' (univ : Set (E2 × ℝ)) = _
      rw [preimage_univ, inter_univ, hPsource]
    have hAtarget : A.target = heightCoordinates.symm '' (P.target ×ˢ I) := by
      rw [OpenPartialHomeomorph.trans_target'']
      change heightCoordinates.symm '' ((univ : Set (E2 × ℝ)) ∩ (P.target ×ˢ I)) = _
      rw [univ_inter]
    have hCs : ContDiffOn ℝ ∞ C C.source := hPs.prodMap contDiff_id.contDiffOn
    have hCi : ContDiffOn ℝ ∞ C.symm C.target := hPi.prodMap contDiff_id.contDiffOn
    have hAs : ContDiffOn ℝ ∞ A A.source :=
      heightCoordinates.symm.contDiff.comp_contDiffOn (hCs.mono inter_subset_left)
    have hAi : ContDiffOn ℝ ∞ A.symm A.target :=
      hCi.comp heightCoordinates.contDiff.contDiffOn (fun _ hy => hy.2)
    have hAform (q : (ℝ × ℝ) × ℝ) : A q = heightCoordinates.symm (P q.1, q.2) := rfl
    have hAcenter : A (0, c) = nestedReferenceDiffeomorph (c - kappa) (pstar : E3) := by
      apply heightCoordinates.injective
      rw [hAform, heightCoordinates.apply_symm_apply, hPzero, hShear, hpCoordinates]
      apply Prod.ext
      · rfl
      · change c = w + ‖vstar‖ ^ 2 + vstar 0 / 32 + (c - kappa)
        rw [hstarSq]
        change c = w + (1 - w ^ 2) + (-Real.sqrt (1 - w ^ 2)) / 32 + (c - kappa)
        dsimp only [kappa]
        ring
    refine ⟨A, hAsource, hAtarget, hAs, hAi, hAcenter, ?_, ?_, fun _ _ => rfl, ?_⟩
    · rintro ⟨s, z⟩ ⟨hs, hz⟩
      rw [hAsource]
      refine ⟨?_, ?_⟩
      · change s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2
        have hs' : s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2 := hs
        nlinarith only [hs', pow_pos hR 2]
      · change c - 8 * b < z ∧ z < c + 8 * b
        constructor <;> linarith [hz.1, hz.2]
    · intro s hs
      rw [hAsource]
      have hsD : s ∈ D := hPsource ▸ hs
      refine ⟨hsD, ?_⟩
      change c - 8 * b < c - s.1 ^ 2 + s.2 ^ 2 ∧
        c - s.1 ^ 2 + s.2 ^ 2 < c + 8 * b
      have hs' : s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2 := hsD
      constructor <;> nlinarith only [hs', hRheight, hb, sq_nonneg s.1, sq_nonneg s.2]
    · rintro ⟨s, z⟩ hq
      have hq' : s ∈ D ∧ z ∈ I := by
        change (s, z) ∈ D ×ˢ I
        rw [← hAsource]
        exact hq
      have hs : s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2 := hq'.1
      have hz : |z - c| < 8 * b := abs_lt.mpr ⟨by linarith [hq'.2.1], by linarith [hq'.2.2]⟩
      have hshift : (s, z - c + kappa) ∈ W := hbuffer s (z - c + kappa) hs.le (by
        rw [show z - c + kappa - kappa = z - c by ring]
        exact hz.le)
      let v : E2 := m.symm s
      let a : ℝ := Real.sqrt (1 - ‖v‖ ^ 2)
      let r : ℝ := z - ‖v‖ ^ 2 - v 0 / 32 - (c - kappa)
      let g : ℝ := c - s.1 ^ 2 + s.2 ^ 2
      have hsTarget : s ∈ m.target := hDtarget hq'.1
      have hvSource : v ∈ m.source := m.map_target hsTarget
      have hvNorm : ‖v‖ < 1 := mem_ball_zero_iff.mp (hm_source hvSource)
      have haPos : 0 < a := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg v])
      have haSq' : a ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg v])
      have hrHalf : w / 2 < r := by
        have hh : w / 2 < residual (s, z - c + kappa) := hshift.2
        dsimp only [residual] at hh
        dsimp only [r, v]
        linarith only [hh]
      have hrPos : 0 < r := by linarith only [hrHalf, hw0]
      have hgraph : g = ‖v‖ ^ 2 + a + v 0 / 32 + (c - kappa) := by
        have hh := hm_height v hvSource
        have hmvs : m v = s := m.right_inv hsTarget
        rw [hmvs] at hh
        change ‖v‖ ^ 2 + a + v 0 / 32 = kappa - s.1 ^ 2 + s.2 ^ 2 at hh
        dsimp only [g]
        linarith only [hh]
      have hfactor : ‖v‖ ^ 2 + r ^ 2 - 1 = (z - g) * (r + a) := by
        have hdiff : r - a = z - g := by dsimp only [r]; linarith only [hgraph]
        calc
          ‖v‖ ^ 2 + r ^ 2 - 1 = (r - a) * (r + a) := by nlinarith only [haSq']
          _ = (z - g) * (r + a) := by rw [hdiff]
      have hpositive : 0 < r + a := add_pos hrPos haPos
      have hEq : (‖v‖ ^ 2 + r ^ 2 = 1 ↔ z = g) := by
        calc
          (‖v‖ ^ 2 + r ^ 2 = 1) ↔ ‖v‖ ^ 2 + r ^ 2 - 1 = 0 := sub_eq_zero.symm
          _ ↔ (z - g) * (r + a) = 0 := by rw [hfactor]
          _ ↔ z - g = 0 := by simp only [mul_eq_zero, hpositive.ne', or_false]
          _ ↔ z = g := sub_eq_zero
      have hLe : (‖v‖ ^ 2 + r ^ 2 ≤ 1 ↔ z ≤ g) := by
        calc
          (‖v‖ ^ 2 + r ^ 2 ≤ 1) ↔ ‖v‖ ^ 2 + r ^ 2 - 1 ≤ 0 := sub_nonpos.symm
          _ ↔ (z - g) * (r + a) ≤ 0 * (r + a) := by rw [hfactor, zero_mul]
          _ ↔ z - g ≤ 0 := mul_le_mul_iff_left₀ hpositive
          _ ↔ z ≤ g := sub_nonpos
      have hLt : (‖v‖ ^ 2 + r ^ 2 < 1 ↔ z < g) := by
        calc
          (‖v‖ ^ 2 + r ^ 2 < 1) ↔ ‖v‖ ^ 2 + r ^ 2 - 1 < 0 := sub_neg.symm
          _ ↔ (z - g) * (r + a) < 0 * (r + a) := by rw [hfactor, zero_mul]
          _ ↔ z - g < 0 := mul_lt_mul_iff_left₀ hpositive
          _ ↔ z < g := sub_neg
      have hreg := hRegions (c - kappa) v z
      have hBoundary : (A (s, z) ∈ (nestedReferenceBallChart (c - kappa)).boundary ↔ z = g) :=
        hreg.2.2.trans hEq
      have hClosed : (A (s, z) ∈ (nestedReferenceBallChart (c - kappa)).closedRegion ↔ z ≤ g) :=
        hreg.2.1.trans hLe
      have hInside : (A (s, z) ∈ (nestedReferenceBallChart (c - kappa)).inside ↔ z < g) :=
        hreg.1.trans hLt
      refine ⟨hAform (s, z), congrArg Prod.snd (heightCoordinates.apply_symm_apply (P s, z)),
        ?_, hBoundary, hClosed, hInside, ?_⟩
      · rw [hAform, hInverseHeight]
        exact hrHalf
      · rw [hClosed]
        exact not_le

end PoincareConjecture.M25.Topology3D
