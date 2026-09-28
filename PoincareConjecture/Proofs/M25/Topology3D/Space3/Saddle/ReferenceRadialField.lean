import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceExteriorCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceSourceVelocity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SphereChartRadialLift
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldChartTransport
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold InnerProductSpace Topology Matrix

namespace PoincareConjecture.M25.Topology3D




theorem exists_nonnested_reference_radial_field
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (a : ℝ) (ha : 0 < a) (haCorrection : 16 / sigma < a ^ 2)
    (haLarge : 8 < a ^ 2)
    (u : UnitTwoSphere) (c rho : ℝ) (hrho : 0 < rho)
    (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hheight : ∀ p : UnitTwoSphere,
      ⟪(u : E3), F (p : E3)⟫_ℝ = c + rho ^ 2 * a ^ 2 *
        (1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
          d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2))) :
    let RF3 := exists_nonnested_reference_exterior_coordinates
      sigma hsigma hsigmaSmall d hd hdNear hdZero hdBounds hdDeriv
      a ha haCorrection haLarge
    let Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere :=
      Classical.choose (Classical.choose_spec RF3)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let nu : ℝ := rho ^ 2 * a ^ 2
    let b : ℝ := 1 / (128 * a ^ 2)
    let f : UnitTwoSphere → ℝ := fun p =>
      1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
        d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
    let q : UnitTwoSphere → ℝ := fun p =>
      ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
    let j : UnitTwoSphere → E3 := fun p => F (p : E3)
    let eps : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let Z : Fin 4 → ℝ → ℝ → E3 := fun k h R =>
      !₂[sx k * Real.sqrt (R ^ 2 / a ^ 2 + h),
        sy k * Real.sqrt (R ^ 2 / a ^ 2 - h),
        -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)]
    let T : Fin 2 → Set E3 := fun i => {y : E3 |
      1 / 2 < ‖F.symm y‖ ∧ ‖F.symm y‖ < 3 / 2 ∧
        sphereDirection (F.symm y) ∈ (Q i).target}
    let E : ℝ → Set E3 := fun h =>
      j '' {p : UnitTwoSphere | f p = h ∧ 2 / a ^ 2 ≤ q p}
    let Ei : Fin 2 → ℝ → Set E3 := fun i h =>
      j '' {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧
        f p = h ∧ 2 / a ^ 2 ≤ q p}
    ∃ (zeta : ℝ) (Xi : Fin 2 → E3 → E3) (Ci : Fin 2 → Set E3),
    let X : E3 → E3 := fun y => Xi 0 y + Xi 1 y
    0 < zeta ∧ zeta < 1 / 8 ∧ Disjoint (T 0) (T 1) ∧
    (∀ i : Fin 2,
      ContDiff ℝ ∞ (Xi i) ∧ HasCompactSupport (Xi i) ∧
      IsCompact (Ci i) ∧ tsupport (Xi i) ⊆ Ci i ∧
      Ci i ⊆ T i ∩ {y : E3 | |H y - c| < 4 * nu * b}) ∧
    (∀ y : E3, fderiv ℝ (fun z : E3 => ‖F.symm z‖) y (X y) = 0) ∧
    (∀ p : UnitTwoSphere, |f p| ≤ 3 * b → 2 / a ^ 2 ≤ q p →
      H (X (j p)) = 1) ∧
    (∀ h : ℝ, |h| ≤ 3 * b →
      (∀ (i : Fin 2) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        (t, h) ∈ (Q i).source) ∧
      (∀ i : Fin 2, Ei i h = (fun t : ℝ => j (Q i (t, h))) '' Icc (0 : ℝ) 1) ∧
      E h = Ei 0 h ∪ Ei 1 h ∧ Disjoint (Ei 0 h) (Ei 1 h)) ∧
    (∀ (k : Fin 4) (R : ℝ), R ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ h : ℝ, |h| ≤ 3 * b →
        ‖Z k h R‖ = 1 ∧ H (F (Z k h R)) = c + nu * h) ∧
    ∀ (k : Fin 4) (R : ℝ), R ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
      ∀ (h s : ℝ), |h| ≤ 2 * b → |s| ≤ zeta →
        HasDerivAt (fun t : ℝ => F ((1 + s) • Z k (t / nu) R))
          (X (F ((1 + s) • Z k h R))) (nu * h) := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let RF3 := exists_nonnested_reference_exterior_coordinates
    sigma hsigma hsigmaSmall d hd hdNear hdZero hdBounds hdDeriv a ha haCorrection haLarge
  let Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere :=
    Classical.choose (Classical.choose_spec RF3)
  obtain ⟨_heta, _hetaSmall, hQall, _hProduct, _hClosed, _hRegular, hCompare, hQends⟩ :=
    Classical.choose_spec (Classical.choose_spec RF3)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let nu : ℝ := rho ^ 2 * a ^ 2
  let b : ℝ := 1 / (128 * a ^ 2)
  let f : UnitTwoSphere → ℝ := fun p =>
    1 + (p : E3) 2 - ((p : E3) 1) ^ 2 + d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
  let q : UnitTwoSphere → ℝ := fun p => ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
  let j : UnitTwoSphere → E3 := fun p => F (p : E3)
  let eps : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let Z : Fin 4 → ℝ → ℝ → E3 := fun k h R =>
    !₂[sx k * Real.sqrt (R ^ 2 / a ^ 2 + h),
      sy k * Real.sqrt (R ^ 2 / a ^ 2 - h), -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)]
  let T : Fin 2 → Set E3 := fun i => {y : E3 | 1 / 2 < ‖F.symm y‖ ∧
    ‖F.symm y‖ < 3 / 2 ∧ sphereDirection (F.symm y) ∈ (Q i).target}
  let E : ℝ → Set E3 := fun h => j '' {p : UnitTwoSphere | f p = h ∧ 2 / a ^ 2 ≤ q p}
  let Ei : Fin 2 → ℝ → Set E3 := fun i h =>
    j '' {p : UnitTwoSphere | 0 < eps i * (p : E3) 1 ∧ f p = h ∧ 2 / a ^ 2 ≤ q p}
  let I : Set ℝ := Ioo (-4 * b) (4 * b)
  let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
  let theta : ℝ → ℝ → ℝ := fun h R =>
    Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
  let A : ℝ → ℝ := fun h => 2 * Real.pi - 2 * theta h 1
  let phi : ℝ × ℝ → ℝ := fun z => theta z.2 1 + A z.2 * z.1
  let U : Set (ℝ × ℝ) := {z | z.2 ∈ I ∧
    theta z.2 (1 / 4) < phi z ∧ phi z < 2 * Real.pi - theta z.2 (1 / 4)}
  let tR : ℝ → ℝ → ℝ := fun h R => (theta h R - theta h 1) / A h
  let D : Set (ℝ × ℝ) := Icc (29 / 32 : ℝ) (35 / 32) ×ˢ Icc (-3 * b) (3 * b)
  let K0 : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (-3 * b) (3 * b)) ∪
    ((fun p : ℝ × ℝ => (tR p.2 p.1, p.2)) '' D) ∪
    ((fun p : ℝ × ℝ => (1 - tR p.2 p.1, p.2)) '' D)
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha256 : 256 < a ^ 2 := by
    have hh := (div_lt_iff₀ hsigma).mp haCorrection
    have hb' := mul_le_mul_of_nonneg_left hsigmaSmall ha2.le
    nlinarith only [hh, hb']
  have hnu : 0 < nu := mul_pos (sq_pos_of_pos hrho) ha2
  have hb : 0 < b := by dsimp [b]; positivity
  have hI3 (h : ℝ) (hh : |h| ≤ 3 * b) : h ∈ I :=
    ⟨by linarith only [(abs_le.mp hh).1, hb], by linarith only [(abs_le.mp hh).2, hb]⟩
  obtain ⟨_hU, hK0, hK0U, v, hv, h01, _hvEnds, hvTracks⟩ :=
    exists_nonnested_reference_source_velocity a ha ha256
  change IsCompact K0 at hK0
  change K0 ⊆ U at hK0U
  change ContDiffOn ℝ ∞ v U at hv
  have hQs (i : Fin 2) : (Q i).source = U := (hQall i).1
  have hQt (i : Fin 2) : (Q i).target = {p : UnitTwoSphere |
      f p ∈ I ∧ 0 < eps i * (p : E3) 1 ∧ 1 / (8 * a ^ 2) < q p} := (hQall i).2.1
  have hQh (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : f (Q i z) = z.2 :=
    (hQall i).2.2.2.2.2.2 z hz
  have hQsrc (i : Fin 2) {z : ℝ × ℝ} (hz : z ∈ U) : z ∈ (Q i).source := by
    rw [hQs i]; exact hz
  have hQmem (i : Fin 2) (p : UnitTwoSphere) (hh : |f p| ≤ 3 * b)
      (hq : 2 / a ^ 2 ≤ q p) (hs : 0 < eps i * (p : E3) 1) : p ∈ (Q i).target := by
    rw [hQt i]
    refine ⟨hI3 _ hh, hs, lt_of_lt_of_le ?_ hq⟩
    have hlt := div_lt_div_of_pos_right (by norm_num : (1 / 8 : ℝ) < 2) ha2
    simpa only [div_div] using hlt
  have hjinj : Injective j := fun p p' hh =>
    Subtype.ext (F.injective hh)
  have hJheight (p : UnitTwoSphere) : H (j p) = c + nu * f p := hheight p
  have hTdis : Disjoint (T 0) (T 1) := by
    apply disjoint_left.mpr
    intro y h0 h1
    have h0' := h0.2.2
    have h1' := h1.2.2
    rw [hQt 0] at h0'
    rw [hQt 1] at h1'
    have hp := h0'.2.1
    have hn := h1'.2.1
    norm_num [eps] at hp hn
    linarith only [hp, hn]
  have hCharts (i : Fin 2) := exists_sphere_chart_radial_lift F (Q i)
    (by simpa only [hQs i] using (hQall i).2.2.1)
    (by simpa only [hQt i] using (hQall i).2.2.2.1)
  choose C hCs hCt hCsm hCism hCform _hCinv hCnorm _hCdir using hCharts
  have hCs' (i : Fin 2) : (C i).source = U ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2) := by
    rw [hCs i, hQs i]
  have hCt' (i : Fin 2) : (C i).target = T i := hCt i
  have hCcenter (i : Fin 2) (z : ℝ × ℝ) : C i (z, 0) = j (Q i z) := by
    simp only [hCform, add_zero, one_smul, j]
  have hKheight (z : ℝ × ℝ) (hz : z ∈ K0) : |z.2| ≤ 3 * b := by
    rcases hz with (hz | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact abs_le.mpr ⟨by linarith only [hz.2.1], hz.2.2⟩
    · exact abs_le.mpr ⟨by linarith only [hp.2.1], hp.2.2⟩
    · exact abs_le.mpr ⟨by linarith only [hp.2.1], hp.2.2⟩
  let Band : Set E3 := {y : E3 | |H y - c| < 4 * nu * b}
  let O : Fin 2 → Set ((ℝ × ℝ) × ℝ) := fun i => (C i).source ∩ (C i) ⁻¹' Band
  have hBand : IsOpen Band := isOpen_lt (H.continuous.sub continuous_const).abs continuous_const
  have hO (i : Fin 2) : IsOpen (O i) := (C i).isOpen_inter_preimage hBand
  have hKzero (i : Fin 2) : K0 ×ˢ ({0} : Set ℝ) ⊆ O i := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    have hs0 : s = 0 := mem_singleton_iff.mp hs
    subst s
    refine ⟨?_, ?_⟩
    · rw [hCs' i]
      exact ⟨hK0U hz, by norm_num⟩
    · change |H (C i (z, 0)) - c| < 4 * nu * b
      rw [hCcenter, hJheight, hQh i z (hK0U hz), add_sub_cancel_left,
        abs_mul, abs_of_pos hnu]
      have hl := mul_le_mul_of_nonneg_left (hKheight z hz) hnu.le
      nlinarith only [hl, mul_pos hnu hb]
  obtain ⟨W, J, _hW, hJ, hKW, h0J, hWJ⟩ := generalized_tube_lemma hK0
    isCompact_singleton ((hO 0).inter (hO 1))
    (fun z hz => ⟨hKzero 0 hz, hKzero 1 hz⟩)
  obtain ⟨delta, hdelta, hdeltaJ⟩ := Metric.isOpen_iff.mp hJ 0 (h0J (mem_singleton 0))
  let zeta : ℝ := min (1 / 16) (delta / 4)
  have hzeta : 0 < zeta := lt_min (by norm_num) (by positivity)
  have hzetaSmall : zeta < 1 / 8 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hzetaDelta : 2 * zeta < delta := by
    have hh := min_le_right (1 / 16 : ℝ) (delta / 4)
    change zeta ≤ delta / 4 at hh
    linarith only [hh, hdelta]
  let K : Set ((ℝ × ℝ) × ℝ) := K0 ×ˢ Icc (-2 * zeta) (2 * zeta)
  have hK : IsCompact K := hK0.prod isCompact_Icc
  have hKO (i : Fin 2) : K ⊆ O i := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    have hsj : s ∈ J := hdeltaJ (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith only [hs.1, hzetaDelta], by linarith only [hs.2, hzetaDelta]⟩)
    have hp := hWJ ⟨hKW hz, hsj⟩
    fin_cases i
    · exact hp.1
    · exact hp.2
  choose lam hlam hlamC hlamS hlamNear _hlamRange using
    fun i : Fin 2 => exists_compact_smooth_cutoff hK (hO i) (hKO i)
  let V0 : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) := fun z => ((v z.1 / nu, 1 / nu), 0)
  let V : Fin 2 → ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) := fun i z => lam i z • V0 z
  have hV0 (i : Fin 2) : ContDiffOn ℝ ∞ V0 (O i) := by
    have hfst : MapsTo Prod.fst (O i) U := by
      intro z hz
      exact (hCs' i ▸ hz.1).1
    exact (((hv.comp contDiff_fst.contDiffOn hfst).div_const nu).prodMk
      contDiffOn_const).prodMk contDiffOn_const
  have hV (i : Fin 2) : ContDiff ℝ ∞ (V i) :=
    contDiff_cutoff_smul (hO i) (lam i) (hlam i) (hlamS i) V0 (hV0 i)
  have hVc (i : Fin 2) : HasCompactSupport (V i) := (hlamC i).smul_right
  have hVs (i : Fin 2) : tsupport (V i) ⊆ O i :=
    (tsupport_smul_subset_left (lam i) V0).trans (hlamS i)
  have hVsource (i : Fin 2) : tsupport (V i) ⊆ (C i).source :=
    (hVs i).trans inter_subset_left
  have hVplateau (i : Fin 2) (z : (ℝ × ℝ) × ℝ) (hz : z ∈ K) : V i z = V0 z := by
    have heq := (eventually_nhdsSet_iff_forall.mp (hlamNear i) z hz).self_of_nhds
    simp only [V, heq, one_smul]
  have hVlast (i : Fin 2) (z : (ℝ × ℝ) × ℝ) : (V i z).2 = 0 := by simp [V, V0]
  choose Xi hXi hXic hXis hPush using fun i : Fin 2 =>
    exists_chart_field_extension (C i) (hCsm i) (hCism i) (V i) (hV i) (hVc i) (hVsource i)
  let Ci : Fin 2 → Set E3 := fun i => (C i) '' tsupport (V i)
  let X : E3 → E3 := fun y => Xi 0 y + Xi 1 y
  have hCi (i : Fin 2) : IsCompact (Ci i) :=
    (hVc i).isCompact.image_of_continuousOn ((C i).continuousOn.mono (hVsource i))
  have hCiSub (i : Fin 2) : Ci i ⊆ T i ∩ Band := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨hCt' i ▸ (C i).map_source (hVsource i hz), (hVs i hz).2⟩
  have hXiZero (i : Fin 2) (y : E3) (hy : y ∉ T i) : Xi i y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hy ((hCiSub i (hXis i hs)).1)
  have hXpush (i : Fin 2) (z : (ℝ × ℝ) × ℝ) (hz : z ∈ (C i).source) :
      X (C i z) = fderiv ℝ (C i) z (V i z) := by
    have ht : C i z ∈ T i := hCt' i ▸ (C i).map_source hz
    change Xi 0 (C i z) + Xi 1 (C i z) = _
    fin_cases i
    · change Xi 0 (C 0 z) + Xi 1 (C 0 z) = fderiv ℝ (C 0) z (V 0 z)
      rw [hPush 0 z hz, hXiZero 1 (C 0 z) (fun hn => disjoint_left.mp hTdis ht hn), add_zero]
    · change Xi 0 (C 1 z) + Xi 1 (C 1 z) = fderiv ℝ (C 1) z (V 1 z)
      rw [hXiZero 0 (C 1 z) (fun hp => disjoint_left.mp hTdis hp ht), zero_add, hPush 1 z hz]
  let Rad : E3 → ℝ := fun y => ‖F.symm y‖
  have hXiRad (i : Fin 2) (y : E3) : fderiv ℝ Rad y (Xi i y) = 0 := by
    by_cases hy : y ∈ T i
    · have hyt : y ∈ (C i).target := (hCt' i).symm ▸ hy
      let z := (C i).symm y
      have hz : z ∈ (C i).source := (C i).map_target hyt
      have hdf : DifferentiableAt ℝ Rad y := ((contDiffAt_norm ℝ (by
          intro heq
          have hn := hy.1
          rw [heq, norm_zero] at hn
          linarith)).comp y F.symm.contDiff.contDiffAt).differentiableAt (by simp)
      have hdC := ((hCsm i).contDiffAt ((C i).open_source.mem_nhds hz)).differentiableAt (by simp)
      have heq : (fun w => Rad (C i w)) =ᶠ[𝓝 z] fun w : (ℝ × ℝ) × ℝ => 1 + w.2 := by
        filter_upwards [(C i).open_source.mem_nhds hz] with w hw
        exact hCnorm i w hw
      have hl := (show HasFDerivAt Rad (fderiv ℝ Rad y) (C i z) by
        simpa only [z, (C i).right_inv hyt] using hdf.hasFDerivAt).comp z hdC.hasFDerivAt
      have hr0 : HasFDerivAt (fun w : (ℝ × ℝ) × ℝ => 1 + w.2)
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) z :=
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).hasFDerivAt.const_add 1
      have hr := hr0.congr_of_eventuallyEq heq
      have heval := congrArg (fun M : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ => M (V i z)) (hl.unique hr)
      have hP := hPush i z hz
      rw [(C i).right_inv hyt] at hP
      rw [hP]
      exact heval.trans (hVlast i z)
    · rw [hXiZero i y hy, map_zero]
  have hRad (y : E3) : fderiv ℝ Rad y (X y) = 0 := by
    change fderiv ℝ Rad y (Xi 0 y + Xi 1 y) = 0
    rw [map_add, hXiRad 0 y, hXiRad 1 y, zero_add]
  have hUnitChart (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ K0) : H (X (j (Q i z))) = 1 := by
    have hzK : (z, (0 : ℝ)) ∈ K := ⟨hz, by constructor <;> linarith only [hzeta]⟩
    have hzC := (hKO i hzK).1
    let w : ℝ × ℝ := (v z / nu, 1 / nu)
    have hline : HasDerivAt (fun t : ℝ => (z + t • w, (0 : ℝ))) (w, 0) 0 := by
      simpa using ((hasDerivAt_const (0 : ℝ) z).add
        ((hasDerivAt_id (0 : ℝ)).smul_const w)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hdC := ((hCsm i).contDiffAt ((C i).open_source.mem_nhds hzC)).differentiableAt (by simp)
    have hdC' : HasFDerivAt (C i) (fderiv ℝ (C i) (z, 0)) (z + (0 : ℝ) • w, 0) := by
      simpa using hdC.hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => H (C i (z + t • w, 0)))
        (H (fderiv ℝ (C i) (z, 0) (w, 0))) 0 := by
      convert! H.hasFDerivAt.comp_hasDerivAt 0
        (hdC'.comp_hasDerivAt (f := fun t : ℝ => (z + t • w, (0 : ℝ))) 0 hline) using 1
    have hscalar : HasDerivAt (fun t : ℝ => c + nu * (z.2 + t * w.2)) 1 0 := by
      have hdw := (((hasDerivAt_id 0).mul_const w.2).const_add z.2).const_mul nu
      convert! hdw.const_add c using 1
      dsimp only [w]
      field_simp [hnu.ne']
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, (z + t • w, (0 : ℝ)) ∈ (C i).source :=
      hline.continuousAt.eventually (by simpa using (C i).open_source.mem_nhds hzC)
    have heq : (fun t : ℝ => H (C i (z + t • w, 0))) =ᶠ[𝓝 0]
        fun t => c + nu * (z.2 + t * w.2) := by
      filter_upwards [hnear] with t ht
      have htu : z + t • w ∈ U := (hCs' i ▸ ht).1
      rw [hCcenter, hJheight, hQh i _ htu]
      rfl
    rw [← hCcenter, hXpush i (z, 0) hzC, hVplateau i (z, 0) hzK]
    exact hl.unique (hscalar.congr_of_eventuallyEq heq)
  have hQnonzero (p : UnitTwoSphere) (hh : |f p| ≤ 3 * b) (hqp : 2 / a ^ 2 ≤ q p) :
      (p : E3) 1 ≠ 0 := by
    intro hy
    have hp : q p + ((p : E3) 2) ^ 2 = 1 := by
      have hn : ‖(p : E3)‖ ^ 2 = 1 := by rw [norm_eq_of_mem_sphere]; norm_num
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hn
      exact hn
    have hq0 : 0 ≤ q p := by dsimp [q]; positivity
    have hbase : q p / 2 ≤ 1 + (p : E3) 2 := by
      nlinarith only [hp, sq_nonneg (1 + (p : E3) 2)]
    have hf : f p = 1 + (p : E3) 2 + d (q p) := by
      change 1 + (p : E3) 2 - ((p : E3) 1) ^ 2 + d (q p) = _
      rw [hy]; ring
    have hfHi := (abs_le.mp hh).2
    have hqb : 256 * b ≤ q p := by
      have heq : 256 * b = 2 / a ^ 2 := by dsimp [b]; ring
      rw [heq]
      exact hqp
    by_cases hqs : sigma ≤ q p
    · rw [hf, hdZero _ hqs] at hfHi
      nlinarith only [hbase, hqb, hfHi, hb]
    · have hqSmall : q p ≤ 1 / 16 := (le_of_lt (lt_of_not_ge hqs)).trans hsigmaSmall
      have hproduct := mul_nonneg hq0 (sub_nonneg.mpr hqSmall)
      have hdlo := (hdBounds (q p) hq0).1
      rw [hf] at hfHi
      nlinarith only [hbase, hqb, hfHi, hdlo, hproduct, hb]
  have hQcover (p : UnitTwoSphere) (hh : |f p| ≤ 3 * b) (hqp : 2 / a ^ 2 ≤ q p) :
      ∃ i : Fin 2, p ∈ (Q i).target := by
    have hy := hQnonzero p hh hqp
    by_cases hp : 0 < (p : E3) 1
    · exact ⟨0, hQmem 0 p hh hqp (by simpa [eps] using hp)⟩
    · exact ⟨1, hQmem 1 p hh hqp (by
        simpa [eps] using neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hy))⟩
  have hQinverse (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ (Q i).target)
      (hqp : 2 / a ^ 2 ≤ q p) :
      ((Q i).symm p).2 = f p ∧ ((Q i).symm p).1 ∈ Icc (0 : ℝ) 1 := by
    have hs : (Q i).symm p ∈ U := hQs i ▸ (Q i).map_target hp
    have hh := hQh i ((Q i).symm p) hs
    rw [(Q i).right_inv hp] at hh
    refine ⟨hh.symm, ?_⟩
    apply (hCompare i ((Q i).symm p).2 ((Q i).symm p).1 hs).1.mp
    change 2 / a ^ 2 ≤ q (Q i ((Q i).symm p))
    rw [(Q i).right_inv hp]
    exact hqp
  have hUnit (p : UnitTwoSphere) (hh : |f p| ≤ 3 * b) (hqp : 2 / a ^ 2 ≤ q p) :
      H (X (j p)) = 1 := by
    obtain ⟨i, hi⟩ := hQcover p hh hqp
    have hz := hQinverse i p hi hqp
    have hk : (Q i).symm p ∈ K0 := Or.inl (Or.inl
      ⟨hz.2, by
        rw [hz.1]
        exact ⟨by linarith only [(abs_le.mp hh).1], (abs_le.mp hh).2⟩⟩)
    simpa only [(Q i).right_inv hi] using hUnitChart i ((Q i).symm p) hk
  have hCoverage (h : ℝ) (hh : |h| ≤ 3 * b) :
      (∀ (i : Fin 2) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → (t, h) ∈ (Q i).source) ∧
      (∀ i : Fin 2, Ei i h = (fun t : ℝ => j (Q i (t, h))) '' Icc (0 : ℝ) 1) ∧
      E h = Ei 0 h ∪ Ei 1 h ∧ Disjoint (Ei 0 h) (Ei 1 h) := by
    have hsrc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, h) ∈ U :=
      h01 h (hI3 h hh) t ht
    refine ⟨fun i t ht => hQsrc i (hsrc t ht), ?_, ?_, ?_⟩
    · intro i
      ext y; constructor
      · rintro ⟨p, hp, rfl⟩
        have hpm := hQmem i p (hp.2.1.symm ▸ hh) hp.2.2 hp.1
        have hpi := hQinverse i p hpm hp.2.2
        refine ⟨((Q i).symm p).1, hpi.2, ?_⟩
        have heq : (((Q i).symm p).1, h) = (Q i).symm p :=
          Prod.ext rfl (hpi.1.trans hp.2.1).symm
        change j (Q i (((Q i).symm p).1, h)) = j p
        rw [heq, (Q i).right_inv hpm]
      · rintro ⟨t, ht, rfl⟩
        have hu := hsrc t ht
        have hp := (Q i).map_source (hQsrc i hu)
        rw [hQt i] at hp
        exact ⟨Q i (t, h), ⟨hp.2.1, hQh i _ hu, (hCompare i h t hu).1.mpr ht⟩, rfl⟩
    · ext y; constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨i, hi⟩ := hQcover p (hp.1.symm ▸ hh) hp.2
        rw [hQt i] at hi
        fin_cases i
        · exact Or.inl ⟨p, ⟨hi.2.1, hp.1, hp.2⟩, rfl⟩
        · exact Or.inr ⟨p, ⟨hi.2.1, hp.1, hp.2⟩, rfl⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) <;> exact ⟨p, hp.2, rfl⟩
    · apply disjoint_left.mpr
      rintro y ⟨p, hp, hpj⟩ ⟨p', hp', hpj'⟩
      have heq : p = p' := hjinj (hpj.trans hpj'.symm)
      subst p'
      have hpos := hp.1
      have hneg := hp'.1
      norm_num [eps] at hpos hneg
      linarith only [hpos, hneg]
  let label : Fin 4 → Fin 2 := ![0, 0, 1, 1]
  let P : Fin 4 → ℝ → ℝ → ℝ × ℝ := fun k h R =>
    if k = 0 ∨ k = 2 then (tR h R, h) else (1 - tR h R, h)
  have hPorts (k : Fin 4) (R h : ℝ) (hR : R ∈ Ioo (15 / 16 : ℝ) (17 / 16)) (hh : h ∈ I) :
      P k h R ∈ U ∧
      (Q (label k) (P k h R) : E3) = Z k h R ∧
      HasDerivAt (fun x : ℝ => P k x R) (v (P k h R), 1) h := by
    have hR' : R ∈ Ioo (7 / 8 : ℝ) (9 / 8) :=
      ⟨by linarith only [hR.1], by linarith only [hR.2]⟩
    have hv' := hvTracks R hR' h hh
    have h0 := hQends 0 h hh R hR'
    have h1 := hQends 1 h hh R hR'
    change (tR h R, h) ∈ U ∧ (1 - tR h R, h) ∈ U ∧
      HasDerivAt (fun x : ℝ => (tR x R, x)) (v (tR h R, h), 1) h ∧
      HasDerivAt (fun x : ℝ => (1 - tR x R, x))
        (v (1 - tR h R, h), 1) h at hv'
    change (tR h R, h) ∈ U ∧ (1 - tR h R, h) ∈ U ∧
      (Q 0 (tR h R, h) : E3) =
        !₂[eps 0 * Real.sqrt (R ^ 2 / a ^ 2 + h),
          eps 0 * Real.sqrt (R ^ 2 / a ^ 2 - h), -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)] ∧
      (Q 0 (1 - tR h R, h) : E3) =
        !₂[-eps 0 * Real.sqrt (R ^ 2 / a ^ 2 + h),
          eps 0 * Real.sqrt (R ^ 2 / a ^ 2 - h), -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)] at h0
    change (tR h R, h) ∈ U ∧ (1 - tR h R, h) ∈ U ∧
      (Q 1 (tR h R, h) : E3) =
        !₂[eps 1 * Real.sqrt (R ^ 2 / a ^ 2 + h),
          eps 1 * Real.sqrt (R ^ 2 / a ^ 2 - h), -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)] ∧
      (Q 1 (1 - tR h R, h) : E3) =
        !₂[-eps 1 * Real.sqrt (R ^ 2 / a ^ 2 + h),
          eps 1 * Real.sqrt (R ^ 2 / a ^ 2 - h), -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)] at h1
    fin_cases k
    · exact ⟨by simpa [P] using hv'.1,
        by simpa [P, label, eps, Z, sx, sy] using h0.2.2.1,
        by simpa [P] using hv'.2.2.1⟩
    · exact ⟨by simpa [P] using hv'.2.1,
        by simpa [P, label, eps, Z, sx, sy] using h0.2.2.2,
        by simpa [P] using hv'.2.2.2⟩
    · exact ⟨by simpa [P] using hv'.1,
        by simpa [P, label, eps, Z, sx, sy] using h1.2.2.1,
        by simpa [P] using hv'.2.2.1⟩
    · exact ⟨by simpa [P] using hv'.2.1,
        by simpa [P, label, eps, Z, sx, sy] using h1.2.2.2,
        by simpa [P] using hv'.2.2.2⟩
  have hPsnd (k : Fin 4) (h R : ℝ) : (P k h R).2 = h := by
    dsimp only [P]
    split <;> rfl
  have hPK (k : Fin 4) (R h : ℝ) (hR : R ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (hh : |h| ≤ 3 * b) : P k h R ∈ K0 := by
    have hp : (R, h) ∈ D :=
      ⟨⟨by linarith only [hR.1], by linarith only [hR.2]⟩,
        ⟨by linarith only [(abs_le.mp hh).1], (abs_le.mp hh).2⟩⟩
    dsimp only [P]
    split
    · exact Or.inl (Or.inr ⟨(R, h), hp, rfl⟩)
    · exact Or.inr ⟨(R, h), hp, rfl⟩
  have hZ (k : Fin 4) (R : ℝ) (hR : R ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (h : ℝ) (hh : |h| ≤ 3 * b) : ‖Z k h R‖ = 1 ∧ H (F (Z k h R)) = c + nu * h := by
    have hp := hPorts k R h hR (hI3 h hh)
    constructor
    · rw [← hp.2.1, norm_eq_of_mem_sphere]
    · rw [← hp.2.1]
      change H (j (Q (label k) (P k h R))) = c + nu * h
      rw [hJheight, hQh _ _ hp.1, hPsnd]
  refine ⟨zeta, Xi, Ci, hzeta, hzetaSmall, hTdis,
    fun i => ⟨hXi i, hXic i, hCi i, hXis i, hCiSub i⟩,
    hRad, hUnit, hCoverage, hZ, ?_⟩
  intro k R hR h s hh hs
  have hh3 : |h| ≤ 3 * b := by linarith only [hh, hb]
  have hp := hPorts k R h hR (hI3 h hh3)
  let z : (ℝ × ℝ) × ℝ := (P k h R, s)
  have hzK : z ∈ K := ⟨hPK k R h hR hh3,
    ⟨by linarith only [(abs_le.mp hs).1, hzeta], by linarith only [(abs_le.mp hs).2, hzeta]⟩⟩
  have hzC := (hKO (label k) hzK).1
  have hcancel : nu * h / nu = h := by field_simp [hnu.ne']
  have hscalar : HasDerivAt (fun t : ℝ => t / nu) (1 / nu) (nu * h) :=
    (hasDerivAt_id (nu * h)).div_const nu
  have hpath : HasDerivAt (fun t : ℝ => (P k (t / nu) R, s)) (V0 z) (nu * h) := by
    have hdP := hp.2.2.scomp_of_eq (nu * h) hscalar hcancel.symm
    have hcoef : ((1 / nu) • (v (P k h R), 1), (0 : ℝ)) = V0 z := by
      apply Prod.ext
      · apply Prod.ext
        · change (1 / nu) * v (P k h R) = v (P k h R) / nu
          ring
        · change (1 / nu) * 1 = 1 / nu
          ring
      · rfl
    simpa only [Function.comp_def, hcoef] using hdP.prodMk (hasDerivAt_const (nu * h) s)
  have hdC := ((hCsm (label k)).contDiffAt
    ((C (label k)).open_source.mem_nhds hzC)).differentiableAt (by simp)
  have hdC' : HasFDerivAt (C (label k)) (fderiv ℝ (C (label k)) z)
      (P k (nu * h / nu) R, s) := by rw [hcancel]; exact hdC.hasFDerivAt
  have hcomp := hdC'.comp_hasDerivAt (nu * h) hpath
  have heq : (fun t : ℝ => F ((1 + s) • Z k (t / nu) R)) =ᶠ[𝓝 (nu * h)]
      fun t => C (label k) (P k (t / nu) R, s) := by
    have hnear : ∀ᶠ t : ℝ in 𝓝 (nu * h), t / nu ∈ I :=
      hscalar.continuousAt.eventually (by
        change ∀ᶠ y : ℝ in 𝓝 (nu * h / nu), y ∈ I
        rw [hcancel]
        exact isOpen_Ioo.mem_nhds (hI3 h hh3))
    filter_upwards [hnear] with t ht
    rw [hCform, (hPorts k R (t / nu) hR ht).2.1]
  have hzEq : C (label k) z = F ((1 + s) • Z k h R) := by
    rw [hCform, hp.2.1]
  convert! hcomp.congr_of_eventuallyEq heq using 1
  change X (F ((1 + s) • Z k h R)) = fderiv ℝ (C (label k)) z (V0 z)
  rw [← hzEq, hXpush (label k) z hzC, hVplateau (label k) z hzK]

end PoincareConjecture.M25.Topology3D
