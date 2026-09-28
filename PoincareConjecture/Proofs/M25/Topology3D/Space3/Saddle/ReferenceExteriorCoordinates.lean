import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceExteriorBounds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSmoothRestriction
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_nonnested_reference_exterior_coordinates
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (a : ℝ) (ha : 0 < a) (haCorrection : 16 / sigma < a ^ 2)
    (haLarge : 8 < a ^ 2) :
    let L : OpenPartialHomeomorph ℝ ℝ := Classical.choose
      (Classical.choose_spec (Classical.choose_spec
        (exists_nonnested_reference_meridian sigma hsigma hsigmaSmall
          d hd hdNear hdZero hdBounds hdDeriv)))
    let eps : Fin 2 → ℝ := ![1, -1]
    let b : ℝ := 1 / (128 * a ^ 2)
    let I : Set ℝ := Ioo (-4 * b) (4 * b)
    let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
    let theta : ℝ → ℝ → ℝ := fun h R =>
      Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
    let A : ℝ → ℝ := fun h => 2 * Real.pi - 2 * theta h 1
    let phi : ℝ × ℝ → ℝ := fun z => theta z.2 1 + A z.2 * z.1
    let W : ℝ × ℝ → ℝ := fun z => L.symm (-r z.2 * Real.cos (phi z))
    let energy : ℝ × ℝ → ℝ := fun z =>
      1 - (r z.2) ^ 2 * Real.sin (phi z) ^ 2 - (W z) ^ 2
    let U : Set (ℝ × ℝ) := {z | z.2 ∈ I ∧
      theta z.2 (1 / 4) < phi z ∧ phi z < 2 * Real.pi - theta z.2 (1 / 4)}
    let f : UnitTwoSphere → ℝ := fun p =>
      1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
        d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
    let q : UnitTwoSphere → ℝ := fun p =>
      ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
    let V : Fin 2 → Set UnitTwoSphere := fun i =>
      {p | f p ∈ I ∧ 0 < eps i * (p : E3) 1 ∧ 1 / (8 * a ^ 2) < q p}
    let P : Fin 2 → UnitTwoSphere → ℝ := fun i p => Real.pi + Complex.arg
      (((2 * L ((p : E3) 2) : ℝ) : ℂ) -
        ((2 * eps i * (p : E3) 0 : ℝ) : ℂ) * Complex.I)
    ∃ (eta : ℝ) (Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere),
      0 < eta ∧ eta < 1 / 16 ∧
      (∀ i : Fin 2,
        (Q i).source = U ∧ (Q i).target = V i ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (Q i) U ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (Q i).symm (V i) ∧
        (∀ z ∈ U, (Q i z : E3) =
          !₂[eps i * r z.2 * Real.sin (phi z),
            eps i * Real.sqrt (energy z), W z]) ∧
        (∀ p ∈ V i, (Q i).symm p =
          ((P i p - theta (f p) 1) / A (f p), f p)) ∧
        (∀ z ∈ U, f (Q i z) = z.2)) ∧
      Ioo (-eta) (1 + eta) ×ˢ I ⊆ U ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (-2 * b) (2 * b) ⊆ U ∧
      (∀ p : UnitTwoSphere, |f p| < 4 * b → 1 / (8 * a ^ 2) < q p →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0) ∧
      (∀ (i : Fin 2) (h t : ℝ), (t, h) ∈ U →
        (2 / a ^ 2 ≤ q (Q i (t, h)) ↔ t ∈ Icc (0 : ℝ) 1) ∧
        (2 / a ^ 2 < q (Q i (t, h)) ↔ t ∈ Ioo (0 : ℝ) 1)) ∧
      (∀ (i : Fin 2) (h : ℝ), h ∈ I → ∀ R ∈ Ioo (7 / 8 : ℝ) (9 / 8),
        let tR : ℝ := (theta h R - theta h 1) / A h
        (tR, h) ∈ U ∧ (1 - tR, h) ∈ U ∧
        (Q i (tR, h) : E3) =
          !₂[eps i * Real.sqrt (R ^ 2 / a ^ 2 + h),
            eps i * Real.sqrt (R ^ 2 / a ^ 2 - h),
            -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)] ∧
        (Q i (1 - tR, h) : E3) =
          !₂[-eps i * Real.sqrt (R ^ 2 / a ^ 2 + h),
            eps i * Real.sqrt (R ^ 2 / a ^ 2 - h),
            -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)]) := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let H := exists_nonnested_reference_meridian sigma hsigma hsigmaSmall
    d hd hdNear hdZero hdBounds hdDeriv
  let L : OpenPartialHomeomorph ℝ ℝ := Classical.choose
    (Classical.choose_spec (Classical.choose_spec H))
  obtain ⟨he, heSmall, hell, hLs, hLt, hLc, hLi, hLm, hLd, hLf,
    hLe, hLminus, hLhalf, hLzero, hLaff, hLsq⟩ :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
  let eps : Fin 2 → ℝ := ![1, -1]
  let b : ℝ := 1 / (128 * a ^ 2)
  let I : Set ℝ := Ioo (-4 * b) (4 * b)
  let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
  let theta : ℝ → ℝ → ℝ := fun h R =>
    Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
  let A : ℝ → ℝ := fun h => 2 * Real.pi - 2 * theta h 1
  let phi : ℝ × ℝ → ℝ := fun z => theta z.2 1 + A z.2 * z.1
  let W : ℝ × ℝ → ℝ := fun z => L.symm (-r z.2 * Real.cos (phi z))
  let energy : ℝ × ℝ → ℝ := fun z =>
    1 - (r z.2) ^ 2 * Real.sin (phi z) ^ 2 - (W z) ^ 2
  let U : Set (ℝ × ℝ) := {z | z.2 ∈ I ∧
    theta z.2 (1 / 4) < phi z ∧ phi z < 2 * Real.pi - theta z.2 (1 / 4)}
  let f : UnitTwoSphere → ℝ := fun p =>
    1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
      d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
  let q : UnitTwoSphere → ℝ := fun p => ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
  let V : Fin 2 → Set UnitTwoSphere := fun i =>
    {p | f p ∈ I ∧ 0 < eps i * (p : E3) 1 ∧ 1 / (8 * a ^ 2) < q p}
  let Z : Fin 2 → UnitTwoSphere → ℂ := fun i p =>
    ((2 * L ((p : E3) 2) : ℝ) : ℂ) -
      ((2 * eps i * (p : E3) 0 : ℝ) : ℂ) * Complex.I
  let P : Fin 2 → UnitTwoSphere → ℝ := fun i p => Real.pi + Complex.arg (Z i p)
  let v : ℝ := 1 / a ^ 2
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hv : 0 < v := by dsimp [v]; positivity
  have hv8 : v < 1 / 8 := by dsimp [v]; rw [div_lt_iff₀ ha2]; linarith
  have hdiv (x : ℝ) : x / a ^ 2 = x * v := by dsimp [v]; ring
  have hb : 0 < b := by dsimp [b]; positivity
  have hb4 : 4 * b = v / 32 := by dsimp [b, v]; ring
  let Ht : Set ℝ := Icc (-4 * b) (4 * b)
  let Rt : Set ℝ := Icc (1 / 4 : ℝ) (9 / 8)
  let K : ℝ → ℝ := fun w => w ^ 2 + w + d (1 - w ^ 2)
  let S : ℝ → ℝ := fun w => 1 + w + d (1 - w ^ 2)
  let wR : ℝ → ℝ := fun R => -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)
  obtain ⟨hrData, hRadialData, hthetaMono, hSmono, hqCompare⟩ :=
    nonnested_reference_exterior_scalar_bounds sigma hsigma hsigmaSmall
      d hd hdNear hdZero hdBounds hdDeriv a ha haCorrection haLarge
  change StrictMonoOn S (Icc (-1 : ℝ) (1 / 4)) at hSmono
  have hr (h : ℝ) (hh : h ∈ Ht) :
      0 < r h ∧ (r h) ^ 2 = 1 / 4 + h ∧ r h < 3 / 4 :=
    ⟨(hrData h hh).1, (hrData h hh).2.1, (hrData h hh).2.2.1⟩
  have hscale (R : ℝ) (hR : R ∈ Rt) :
      0 < R ^ 2 / a ^ 2 ∧ R ^ 2 / a ^ 2 < 1 / 4 ∧
      2 * R ^ 2 / a ^ 2 < sigma / 2 ∧ v / 16 ≤ R ^ 2 / a ^ 2 := by
    have hs := (hRadialData R hR).1
    have hl : v / 16 = 1 / (16 * a ^ 2) := by dsimp [v]; ring
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hl.trans_le hs.2.2.2⟩
  have htheta (h R : ℝ) (hh : h ∈ Ht) (hR : R ∈ Rt) :
      0 < theta h R ∧ theta h R < Real.pi / 2 ∧
      Real.cos (theta h R) = Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h := by
    have ht := (hRadialData R hR).2.2 h hh
    exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hrd (h : ℝ) (hh : h ∈ Ht) : ContDiffAt ℝ ∞ r h :=
    (hrData h hh).2.2.2
  have htd (R : ℝ) (hR : R ∈ Rt) (h : ℝ) (hh : h ∈ Ht) :
      ContDiffAt ℝ ∞ (fun s => theta s R) h := (hRadialData R hR).2.2 h hh |>.2.2.2
  have hwR (R : ℝ) (hR : R ∈ Rt) :
      -1 < wR R ∧ wR R < -3 / 4 ∧ wR R ∈ L.source ∧
      S (wR R) = R ^ 2 / a ^ 2 ∧ K (wR R) = -R ^ 2 / a ^ 2 ∧
      L (wR R) = -Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) := (hRadialData R hR).2.1
  have hcosWindow (u y : ℝ) (hu : u ∈ Ioo (0 : ℝ) Real.pi)
      (hy : y ∈ Ioo (0 : ℝ) (2 * Real.pi)) :
      (Real.cos y < Real.cos u ↔ y ∈ Ioo u (2 * Real.pi - u)) ∧
      (Real.cos y ≤ Real.cos u ↔ y ∈ Icc u (2 * Real.pi - u)) := by
    by_cases hh : y ≤ Real.pi
    · have hl := Real.strictAntiOn_cos.lt_iff_gt ⟨hy.1.le, hh⟩ ⟨hu.1.le, hu.2.le⟩
      have he := Real.strictAntiOn_cos.le_iff_ge ⟨hy.1.le, hh⟩ ⟨hu.1.le, hu.2.le⟩
      constructor
      · rw [hl]
        exact ⟨fun h => ⟨h, by linarith only [hu.2, hh]⟩, And.left⟩
      · rw [he]
        exact ⟨fun h => ⟨h, by linarith only [hu.2, hh]⟩, And.left⟩
    · have hrng : 2 * Real.pi - y ∈ Icc (0 : ℝ) Real.pi :=
        ⟨by linarith only [hy.2], by linarith only [hh]⟩
      have hl := Real.strictAntiOn_cos.lt_iff_gt hrng ⟨hu.1.le, hu.2.le⟩
      have he := Real.strictAntiOn_cos.le_iff_ge hrng ⟨hu.1.le, hu.2.le⟩
      rw [Real.cos_two_pi_sub] at hl he
      constructor
      · rw [hl]
        constructor
        · intro h; exact ⟨by linarith only [hu.2, hh], by linarith only [h]⟩
        · intro h; linarith only [h.2]
      · rw [he]
        constructor
        · intro h; exact ⟨by linarith only [hu.2, hh], by linarith only [h]⟩
        · intro h; linarith only [h.2]
  have hWdata (z : ℝ × ℝ) (hz : z ∈ U) :
      W z ∈ Ioo (-1 : ℝ) (1 / 4) ∧ W z ∈ L.source ∧
      L (W z) = -r z.2 * Real.cos (phi z) ∧ 0 < energy z ∧
      1 / (8 * a ^ 2) < 1 - (W z) ^ 2 ∧
      (r z.2) ^ 2 * Real.sin (phi z) ^ 2 + K (W z) = z.2 := by
    have hh : z.2 ∈ Ht := ⟨hz.1.1.le, hz.1.2.le⟩
    have hth := htheta z.2 (1 / 4) hh ⟨le_rfl, by norm_num⟩
    have hrh := hr z.2 hh
    have hwr := hwR (1 / 4) ⟨le_rfl, by norm_num⟩
    have hph : phi z ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
      ⟨by linarith only [hth.1, hz.2.1], by linarith only [hth.1, hz.2.2]⟩
    have hc := (hcosWindow (theta z.2 (1 / 4)) (phi z)
      ⟨hth.1, by linarith only [hth.2.1, Real.pi_pos]⟩ hph).1.mpr hz.2
    rw [hth.2.2] at hc
    have hlo : -Real.sqrt (1 / 4 - (1 / 4) ^ 2 / a ^ 2) <
        -r z.2 * Real.cos (phi z) := by
      have hh' := (lt_div_iff₀ hrh.1).mp hc
      nlinarith only [hh']
    have hi : -r z.2 * Real.cos (phi z) ≤ r z.2 := by
      nlinarith only [Real.neg_one_le_cos (phi z), hrh.1]
    have hroot : Real.sqrt (1 / 4 - (1 / 4) ^ 2 / a ^ 2) < 1 / 2 :=
      (Real.sqrt_lt' (by norm_num)).mpr
        (by nlinarith only [(hscale (1 / 4) ⟨le_rfl, by norm_num⟩).1])
    have htarg : -r z.2 * Real.cos (phi z) ∈ L.target := by
      rw [hLt]
      exact ⟨by linarith only [hell, hroot, hlo], hi.trans_lt hrh.2.2⟩
    have hws : W z ∈ L.source := L.map_target htarg
    have hval : L (W z) = -r z.2 * Real.cos (phi z) := L.right_inv htarg
    have hwlo : wR (1 / 4) < W z := (hLm.lt_iff_lt hwr.2.2.1 hws).mp
      (by rw [hwr.2.2.2.2.2, hval]; exact hlo)
    have hwi : W z ∈ Ioo (-1 : ℝ) (1 / 4) :=
      ⟨hwr.1.trans hwlo, (hLs ▸ hws).2⟩
    have hsq := hLsq (W z) hws
    change (L (W z)) ^ 2 = K (W z) + 1 / 4 at hsq
    rw [hval] at hsq
    have htrig := congrArg (fun x : ℝ => (r z.2) ^ 2 * x)
      (Real.sin_sq_add_cos_sq (phi z))
    have hheight : (r z.2) ^ 2 * Real.sin (phi z) ^ 2 + K (W z) = z.2 := by
      nlinarith only [hsq, htrig, hrh.2.1]
    have heq : energy z = S (W z) - z.2 := by
      dsimp only [energy, S]
      dsimp only [K] at hheight
      linarith only [hheight]
    have hSlt := hSmono ⟨hwr.1.le, by linarith only [hwr.2.1]⟩
      ⟨hwi.1.le, hwi.2.le⟩ hwlo
    rw [hwr.2.2.2.1, hdiv] at hSlt
    have hepos : 0 < energy z := by
      have hhi := hh.2
      rw [hb4] at hhi
      rw [heq]
      nlinarith only [hSlt, hhi, hv]
    have hq := (hqCompare (1 / 4) (W z) ⟨le_rfl, by norm_num⟩ hwi).2.mpr hwlo
    have hfrac : 2 * (1 / 4 : ℝ) ^ 2 / a ^ 2 = 1 / (8 * a ^ 2) := by ring
    rw [hfrac] at hq
    exact ⟨hwi, hws, hval, hepos, hq, hheight⟩
  have hpData (p : UnitTwoSphere) (hh : f p ∈ I) (hq : 1 / (8 * a ^ 2) < q p) :
      (p : E3) 2 ∈ Ioo (-1 : ℝ) (1 / 4) ∧ (p : E3) 2 ∈ L.source ∧
      q p = 1 - ((p : E3) 2) ^ 2 ∧
      ((p : E3) 0) ^ 2 + (L ((p : E3) 2)) ^ 2 = (r (f p)) ^ 2 ∧
      0 < ((p : E3) 1) ^ 2 ∧ wR (1 / 4) < (p : E3) 2 := by
    have hn : ‖(p : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp p.property
    have hsum := EuclideanSpace.real_norm_sq_eq (p : E3)
    rw [hn, Fin.sum_univ_three] at hsum
    have hqe : q p = 1 - ((p : E3) 2) ^ 2 := by
      dsimp only [q]
      nlinarith only [hsum]
    have hq0 : 0 ≤ q p := by dsimp only [q]; positivity
    have hqpos : 0 < q p := (by positivity : (0 : ℝ) < 1 / (8 * a ^ 2)).trans hq
    have hwlo : -1 < (p : E3) 2 := by
      nlinarith only [hqe, hqpos, sq_nonneg ((p : E3) 2 + 1)]
    have hht : f p ∈ Ht := ⟨hh.1.le, hh.2.le⟩
    have hhi : f p < v / 32 := by rw [← hb4]; exact hh.2
    have hheight : f p = ((p : E3) 0) ^ 2 + K ((p : E3) 2) := by
      change 1 + (p : E3) 2 - ((p : E3) 1) ^ 2 + d (q p) = _
      rw [hqe]
      dsimp only [K]
      nlinarith only [hsum]
    have hwhi : (p : E3) 2 < 1 / 4 := by
      by_contra hw
      by_cases hsmall : sigma ≤ q p
      · have hz := hdZero _ hsmall
        rw [hqe] at hz
        dsimp only [K] at hheight
        rw [hz] at hheight
        nlinarith only [hheight, hhi, hv8, hw, sq_nonneg ((p : E3) 0),
          sq_nonneg ((p : E3) 2)]
      · have hql : q p ≤ 1 / 16 := (lt_of_not_ge hsmall).le.trans hsigmaSmall
        have hw3 : 3 / 4 < (p : E3) 2 := by
          nlinarith only [hqe, hql, hw, sq_nonneg ((p : E3) 2 - 3 / 4)]
        have hdb := (hdBounds _ hq0).1
        have hqsq : (q p) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
          (sq_le_sq₀ hq0 (by norm_num)).mpr hql
        have hyq : ((p : E3) 1) ^ 2 ≤ q p := by
          dsimp only [q]; nlinarith only [sq_nonneg ((p : E3) 0)]
        have hf : f p = 1 + (p : E3) 2 - ((p : E3) 1) ^ 2 + d (q p) := rfl
        nlinarith only [hf, hw3, hdb, hqsq, hyq, hql, hhi, hv8]
    have hw : (p : E3) 2 ∈ Ioo (-1 : ℝ) (1 / 4) := ⟨hwlo, hwhi⟩
    have hws : (p : E3) 2 ∈ L.source := by
      rw [hLs]
      exact ⟨by linarith only [he, hwlo], hwhi⟩
    have hcirc : ((p : E3) 0) ^ 2 + (L ((p : E3) 2)) ^ 2 = (r (f p)) ^ 2 := by
      have hls := hLsq ((p : E3) 2) hws
      change (L ((p : E3) 2)) ^ 2 = K ((p : E3) 2) + 1 / 4 at hls
      linarith only [hls, hheight, (hr (f p) hht).2.1]
    have hfrac : 2 * (1 / 4 : ℝ) ^ 2 / a ^ 2 = 1 / (8 * a ^ 2) := by ring
    have hwr := hwR (1 / 4) ⟨le_rfl, by norm_num⟩
    have hwgt : wR (1 / 4) < (p : E3) 2 :=
      (hqCompare (1 / 4) _ ⟨le_rfl, by norm_num⟩ hw).2.mp (by rwa [hfrac, ← hqe])
    have hSgt := hSmono ⟨hwr.1.le, by linarith only [hwr.2.1]⟩
      ⟨hwlo.le, hwhi.le⟩ hwgt
    rw [hwr.2.2.2.1, hdiv] at hSgt
    have hys : ((p : E3) 1) ^ 2 = S ((p : E3) 2) - f p := by
      dsimp only [S, K] at hheight ⊢
      nlinarith only [hheight, hsum]
    refine ⟨hw, hws, hqe, hcirc, ?_, hwgt⟩
    rw [hys]
    nlinarith only [hSgt, hhi, hv]
  have heps (i : Fin 2) : (eps i) ^ 2 = 1 := by fin_cases i <;> norm_num [eps]
  have hepsne (i : Fin 2) : eps i ≠ 0 := by fin_cases i <;> norm_num [eps]
  have hPdata (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ V i) :
      Z i p ∈ Complex.slitPlane ∧ P i p ∈ Ioo (0 : ℝ) (2 * Real.pi) ∧
      Real.cos (P i p) = -L ((p : E3) 2) / r (f p) ∧
      Real.sin (P i p) = eps i * (p : E3) 0 / r (f p) ∧
      P i p ∈ Ioo (theta (f p) (1 / 4)) (2 * Real.pi - theta (f p) (1 / 4)) := by
    have hh : f p ∈ Ht := ⟨hp.1.1.le, hp.1.2.le⟩
    have hdP := hpData p hp.1 hp.2.2
    have hrh := hr (f p) hh
    have hth := htheta (f p) (1 / 4) hh ⟨le_rfl, by norm_num⟩
    have hwr := hwR (1 / 4) ⟨le_rfl, by norm_num⟩
    have hRe : (Z i p).re = 2 * L ((p : E3) 2) := by simp [Z]
    have hIm : (Z i p).im = -2 * eps i * (p : E3) 0 := by simp [Z]
    have hsq : ‖Z i p‖ ^ 2 = (2 * r (f p)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hRe, hIm]
      have he := congrArg (fun x : ℝ => 4 * x * ((p : E3) 0) ^ 2) (heps i)
      nlinarith only [hdP.2.2.2.1, he]
    have hNorm : ‖Z i p‖ = 2 * r (f p) := by
      nlinarith only [hsq, norm_nonneg (Z i p), hrh.1]
    have hZne : Z i p ≠ 0 := norm_pos_iff.mp (hNorm ▸ mul_pos (by norm_num) hrh.1)
    have hLower : -Real.sqrt (1 / 4 - (1 / 4) ^ 2 / a ^ 2) < L ((p : E3) 2) := by
      have hm := hLm hwr.2.2.1 hdP.2.1 hdP.2.2.2.2.2
      rwa [hwr.2.2.2.2.2] at hm
    have hroot : Real.sqrt (1 / 4 - (1 / 4) ^ 2 / a ^ 2) < r (f p) :=
      (div_lt_one hrh.1).mp (Real.arccos_pos.mp hth.1)
    have hSlit : Z i p ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff, hRe, hIm]
      by_cases hx : (p : E3) 0 = 0
      · left
        have hs : (L ((p : E3) 2)) ^ 2 = (r (f p)) ^ 2 := by
          simpa only [hx, zero_pow (by norm_num : 2 ≠ 0), zero_add] using hdP.2.2.2.1
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
        · rw [he]; exact mul_pos (by norm_num) hrh.1
        · exfalso; linarith only [he, hLower, hroot]
      · exact Or.inr (mul_ne_zero (mul_ne_zero (by norm_num) (hepsne i)) hx)
    have hRange : P i p ∈ Ioo (0 : ℝ) (2 * Real.pi) := by
      have hlo := Complex.neg_pi_lt_arg (Z i p)
      have hhi := lt_of_le_of_ne (Complex.arg_le_pi (Z i p))
        (Complex.slitPlane_arg_ne_pi hSlit)
      dsimp only [P]
      exact ⟨by linarith only [hlo], by linarith only [hhi]⟩
    have hCos : Real.cos (P i p) = -L ((p : E3) 2) / r (f p) := by
      dsimp only [P]
      rw [add_comm, Real.cos_add_pi, Complex.cos_arg hZne, hRe, hNorm]
      ring
    have hSin : Real.sin (P i p) = eps i * (p : E3) 0 / r (f p) := by
      dsimp only [P]
      rw [add_comm, Real.sin_add_pi, Complex.sin_arg, hIm, hNorm]
      ring
    refine ⟨hSlit, hRange, hCos, hSin, ?_⟩
    apply (hcosWindow (theta (f p) (1 / 4)) (P i p)
      ⟨hth.1, by linarith only [hth.2.1, Real.pi_pos]⟩ hRange).1.mp
    rw [hCos, hth.2.2]
    exact (div_lt_div_iff_of_pos_right hrh.1).mpr (by linarith only [hLower])
  let T : Fin 2 → ℝ × ℝ → E3 := fun i z =>
    !₂[eps i * r z.2 * Real.sin (phi z), eps i * Real.sqrt (energy z), W z]
  have hTsphere (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : T i z ∈ sphere (0 : E3) 1 := by
    have he := Real.sq_sqrt (hWdata z hz).2.2.2.1.le
    have hn : ‖T i z‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      change (eps i * r z.2 * Real.sin (phi z)) ^ 2 +
        (eps i * Real.sqrt (energy z)) ^ 2 + (W z) ^ 2 = 1
      simp only [mul_pow, heps, one_mul, he]
      dsimp only [energy]
      ring
    rw [mem_sphere_zero_iff_norm]
    nlinarith only [hn, norm_nonneg (T i z)]
  let base : UnitTwoSphere := Classical.choice
    ((NormedSpace.sphere_nonempty (E := E3) (x := 0)).mpr zero_le_one).coe_sort
  let F : Fin 2 → ℝ × ℝ → UnitTwoSphere := fun i z =>
    if hz : z ∈ U then ⟨T i z, hTsphere i z hz⟩ else base
  have hFcoe (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : (F i z : E3) = T i z := by
    simp only [F, dif_pos hz]
  have hFdata (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) :
      f (F i z) = z.2 ∧ q (F i z) = 1 - (W z) ^ 2 ∧ F i z ∈ V i := by
    have hw := hWdata z hz
    have he := Real.sq_sqrt hw.2.2.2.1.le
    have hq : q (F i z) = 1 - (W z) ^ 2 := by
      change ((F i z : E3) 0) ^ 2 + ((F i z : E3) 1) ^ 2 = _
      rw [hFcoe i z hz]
      change (eps i * r z.2 * Real.sin (phi z)) ^ 2 +
        (eps i * Real.sqrt (energy z)) ^ 2 = _
      simp only [mul_pow, heps, one_mul, he]
      dsimp only [energy]
      ring
    have hf : f (F i z) = z.2 := by
      change 1 + (F i z : E3) 2 - ((F i z : E3) 1) ^ 2 + d (q (F i z)) = _
      rw [hq, hFcoe i z hz]
      change 1 + W z - (eps i * Real.sqrt (energy z)) ^ 2 + d (1 - (W z) ^ 2) = _
      rw [mul_pow, heps, one_mul, he]
      have hh := hw.2.2.2.2.2
      dsimp only [energy, K] at hh ⊢
      linarith only [hh]
    refine ⟨hf, hq, ?_⟩
    change f (F i z) ∈ I ∧ 0 < eps i * (F i z : E3) 1 ∧
      1 / (8 * a ^ 2) < q (F i z)
    rw [hf, hq, hFcoe i z hz]
    refine ⟨hz.1, ?_, hw.2.2.2.2.1⟩
    change 0 < eps i * (eps i * Real.sqrt (energy z))
    rw [← mul_assoc, ← pow_two, heps, one_mul]
    exact Real.sqrt_pos.mpr hw.2.2.2.1
  have hA (h : ℝ) (hh : h ∈ Ht) : 0 < A h := by
    have ht := htheta h 1 hh ⟨by norm_num, by norm_num⟩
    dsimp only [A]
    linarith only [ht.2.1, Real.pi_pos]
  let G : Fin 2 → UnitTwoSphere → ℝ × ℝ := fun i p =>
    ((P i p - theta (f p) 1) / A (f p), f p)
  have hGphi (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ V i) : phi (G i p) = P i p := by
    have hh : A (f p) ≠ 0 := (hA (f p) ⟨hp.1.1.le, hp.1.2.le⟩).ne'
    dsimp only [phi, G]
    field_simp
    ring
  have hGmem (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ V i) : G i p ∈ U := by
    change f p ∈ I ∧ theta (f p) (1 / 4) < phi (G i p) ∧
      phi (G i p) < 2 * Real.pi - theta (f p) (1 / 4)
    rw [hGphi i p hp]
    exact ⟨hp.1, (hPdata i p hp).2.2.2.2⟩
  have hFG (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ V i) : F i (G i p) = p := by
    have hpd := hPdata i p hp
    have hsd := hpData p hp.1 hp.2.2
    have hrh := hr (f p) ⟨hp.1.1.le, hp.1.2.le⟩
    have hW : W (G i p) = (p : E3) 2 := by
      dsimp only [W]
      rw [hGphi i p hp]
      change L.symm (-r (f p) * Real.cos (P i p)) = _
      rw [hpd.2.2.1]
      have hc : -r (f p) * (-L ((p : E3) 2) / r (f p)) = L ((p : E3) 2) := by
        field_simp [hrh.1.ne']
      rw [hc]
      exact L.left_inv hsd.2.1
    have hX : eps i * r (f p) * Real.sin (P i p) = (p : E3) 0 := by
      rw [hpd.2.2.2.1]
      calc
        eps i * r (f p) * (eps i * (p : E3) 0 / r (f p)) =
            (eps i) ^ 2 * (p : E3) 0 := by field_simp [hrh.1.ne']
        _ = (p : E3) 0 := by rw [heps, one_mul]
    have hen : energy (G i p) = ((p : E3) 1) ^ 2 := by
      have hxs := congrArg (fun x : ℝ => x ^ 2) hX
      simp only [mul_pow, heps, one_mul] at hxs
      dsimp only [energy]
      rw [hW, hGphi i p hp]
      change 1 - (r (f p)) ^ 2 * Real.sin (P i p) ^ 2 - ((p : E3) 2) ^ 2 = _
      have hq := hsd.2.2.1
      dsimp only [q] at hq
      linarith only [hxs, hq]
    have hY : eps i * Real.sqrt (((p : E3) 1) ^ 2) = (p : E3) 1 := by
      rw [Real.sqrt_sq_eq_abs]
      have hs : 0 < eps i * (p : E3) 1 := hp.2.1
      fin_cases i
      · norm_num [eps] at hs ⊢
        exact hs.le
      · norm_num [eps] at hs ⊢
        rw [abs_of_neg (by linarith only [hs])]
        ring
    apply Subtype.ext
    rw [hFcoe i (G i p) (hGmem i p hp)]
    ext j
    fin_cases j
    · change eps i * r (f p) * Real.sin (phi (G i p)) = _
      rw [hGphi i p hp]
      exact hX
    · change eps i * Real.sqrt (energy (G i p)) = _
      rw [hen]
      exact hY
    · exact hW
  have hGF (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : G i (F i z) = z := by
    have hw := hWdata z hz
    have hrh := hr z.2 ⟨hz.1.1.le, hz.1.2.le⟩
    have ht := htheta z.2 (1 / 4) ⟨hz.1.1.le, hz.1.2.le⟩ ⟨le_rfl, by norm_num⟩
    have harg : phi z - Real.pi ∈ Ioc (-Real.pi) Real.pi :=
      ⟨by linarith only [ht.1, hz.2.1], by linarith only [ht.1, hz.2.2]⟩
    have hZform : Z i (F i z) = ((2 * r z.2 : ℝ) : ℂ) *
        ((Real.cos (phi z - Real.pi) : ℂ) +
          (Real.sin (phi z - Real.pi) : ℂ) * Complex.I) := by
      have he := congrArg (fun x : ℝ => x * (r z.2 * Real.sin (phi z))) (heps i)
      apply Complex.ext <;>
        simp only [Z, hFcoe i z hz, T, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero, zero_sub]
      · change 2 * L (W z) = 2 * r z.2 * Real.cos (phi z - Real.pi)
        rw [hw.2.2.1, Real.cos_sub_pi]
        ring
      · change -(2 * eps i * (eps i * r z.2 * Real.sin (phi z))) =
          2 * r z.2 * Real.sin (phi z - Real.pi)
        rw [Real.sin_sub_pi]
        nlinarith only [he]
    have hP : P i (F i z) = phi z := by
      dsimp only [P]
      have har := Complex.arg_mul_cos_add_sin_mul_I (r := 2 * r z.2)
        (mul_pos (by norm_num) hrh.1) harg
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at har
      rw [hZform, har]
      ring
    apply Prod.ext
    · change (P i (F i z) - theta (f (F i z)) 1) / A (f (F i z)) = z.1
      rw [hP, (hFdata i z hz).1]
      dsimp only [phi]
      field_simp [(hA z.2 ⟨hz.1.1.le, hz.1.2.le⟩).ne']
      ring
    · exact (hFdata i z hz).1
  have hAd (h : ℝ) (hh : h ∈ Ht) : ContDiffAt ℝ ∞ A h :=
    contDiffAt_const.sub (contDiffAt_const.mul (htd 1 ⟨by norm_num, by norm_num⟩ h hh))
  have hphid (z : ℝ × ℝ) (hz : z.2 ∈ I) : ContDiffAt ℝ ∞ phi z := by
    have hh : z.2 ∈ Ht := ⟨hz.1.le, hz.2.le⟩
    exact ((htd 1 ⟨by norm_num, by norm_num⟩ z.2 hh).comp z contDiffAt_snd).add
      (((hAd z.2 hh).comp z contDiffAt_snd).mul contDiffAt_fst)
  have hUopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hc := (htd (1 / 4) ⟨le_rfl, by norm_num⟩ z.2
      ⟨hz.1.1.le, hz.1.2.le⟩).comp z contDiffAt_snd
    have hp := hphid z hz.1
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hz.1),
      hc.continuousAt.eventually_lt hp.continuousAt hz.2.1,
      hp.continuousAt.eventually_lt (continuousAt_const.sub hc.continuousAt) hz.2.2] with y hy hl hr
    exact ⟨hy, hl, hr⟩
  have hTsm (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : ContDiffAt ℝ ∞ (T i) z := by
    have hrz := (hrd z.2 ⟨hz.1.1.le, hz.1.2.le⟩).comp z contDiffAt_snd
    have hpz := hphid z hz.1
    have hw := hWdata z hz
    have harg : -r z.2 * Real.cos (phi z) ∈ L.target := by
      rw [← hw.2.2.1]
      exact L.map_source hw.2.1
    have hWsm : ContDiffAt ℝ ∞ W z :=
      (hLi.contDiffAt (L.open_target.mem_nhds harg)).comp z (hrz.neg.mul hpz.cos)
    have he : ContDiffAt ℝ ∞ energy z :=
      (contDiffAt_const.sub ((hrz.pow 2).mul (hpz.sin.pow 2))).sub (hWsm.pow 2)
    apply (contDiffAt_piLp 2).mpr
    intro j
    fin_cases j
    · exact (contDiffAt_const.mul hrz).mul hpz.sin
    · exact contDiffAt_const.mul (he.sqrt hw.2.2.2.1.ne')
    · exact hWsm
  have hFsm (i : Fin 2) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (F i) U := by
    apply contMDiffOn_sphere_of_coe hUopen (F i)
    apply ContDiffOn.contMDiffOn
    intro z hz
    have heq : (fun y => (F i y : E3)) =ᶠ[𝓝 z] T i := by
      filter_upwards [hUopen.mem_nhds hz] with y hy
      exact hFcoe i y hy
    exact ((hTsm i z hz).congr_of_eventuallyEq heq).contDiffWithinAt
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : E3 => x j) := contDiff_piLp_apply 2
  have hcm (j : Fin 3) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p : UnitTwoSphere => (p : E3) j) := (hc j).contMDiff.comp contMDiff_coe_sphere
  have hfm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    ((((contDiff_const.add (hc 2)).sub ((hc 1).pow 2)).add
      (hd.comp (((hc 0).pow 2).add ((hc 1).pow 2)))).contMDiff).comp contMDiff_coe_sphere
  have hqm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q := ((hcm 0).pow 2).add ((hcm 1).pow 2)
  have hVopen (i : Fin 2) : IsOpen (V i) :=
    (isOpen_Ioo.preimage hfm.continuous).inter
      ((isOpen_lt continuous_const (continuous_const.mul (hcm 1).continuous)).inter
        (isOpen_lt continuous_const hqm.continuous))
  have hGsm (i : Fin 2) : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (G i) (V i) := by
    intro p hp
    have hpd := hpData p hp.1 hp.2.2
    have hh : f p ∈ Ht := ⟨hp.1.1.le, hp.1.2.le⟩
    have hLsm : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun p : UnitTwoSphere => L ((p : E3) 2)) p :=
      (hLc.contDiffAt (L.open_source.mem_nhds hpd.2.1)).contMDiffAt.comp p (hcm 2 p)
    have hZsm : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (Z i) p := by
      have hpairs : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞
          (fun q : UnitTwoSphere => (2 * L ((q : E3) 2), -(2 * eps i * (q : E3) 0))) p :=
        (contMDiffAt_const.mul hLsm).prodMk_space ((contMDiffAt_const.mul (hcm 0 p)).neg)
      convert! Complex.equivRealProdCLM.symm.contDiff.contDiffAt.contMDiffAt.comp p hpairs using 1
      funext q
      apply Complex.ext <;> simp [Z]
    have hlog : ContDiffAt ℝ ∞ Complex.log (Z i p) :=
      (Complex.contDiffAt_log (hPdata i p hp).1).restrict_scalars ℝ
    have harg : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun q => (Z i q).arg) p := by
      have him := Complex.imCLM.contDiff.contDiffAt.contMDiffAt.comp p
        (hlog.contMDiffAt.comp p hZsm)
      simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using him
    exact ((((contMDiffAt_const.add harg).sub
      ((htd 1 ⟨by norm_num, by norm_num⟩ (f p) hh).contMDiffAt.comp p (hfm p))).div₀
      ((hAd (f p) hh).contMDiffAt.comp p (hfm p)) (hA (f p) hh).ne').prodMk_space
      (hfm p)).contMDiffWithinAt
  let Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere := fun i => {
    toFun := F i
    invFun := G i
    source := U
    target := V i
    map_source' := fun z hz => (hFdata i z hz).2.2
    map_target' := hGmem i
    left_inv' := hGF i
    right_inv' := hFG i
    open_source := hUopen
    open_target := hVopen i
    continuousOn_toFun := (hFsm i).continuousOn
    continuousOn_invFun := (hGsm i).continuousOn }
  let m : ℝ → ℝ := fun h => (theta h 1 - theta h (1 / 4)) / A h
  have hmpos (h : ℝ) (hh : h ∈ Ht) : 0 < m h := div_pos
    (sub_pos.mpr (hthetaMono h hh ⟨le_rfl, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num))) (hA h hh)
  have hmcont : ContinuousOn m Ht := by
    intro h hh
    exact ((((htd 1 ⟨by norm_num, by norm_num⟩ h hh).sub
      (htd (1 / 4) ⟨le_rfl, by norm_num⟩ h hh)).div (hAd h hh)
      (hA h hh).ne').continuousAt).continuousWithinAt
  obtain ⟨h0, hh0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show Ht.Nonempty from ⟨0, ⟨by linarith only [hb], by linarith only [hb]⟩⟩) hmcont
  let eta : ℝ := min (1 / 32) (m h0 / 2)
  have heta : 0 < eta := lt_min (by norm_num) (by linarith only [hmpos h0 hh0])
  have hetasmall : eta < 1 / 16 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hrect : Ioo (-eta) (1 + eta) ×ˢ I ⊆ U := by
    intro z hz
    have hh : z.2 ∈ Ht := ⟨hz.2.1.le, hz.2.2.le⟩
    have hlt : eta < m z.2 := (lt_of_le_of_lt (min_le_right _ _)
      (by linarith only [hmpos h0 hh0] : m h0 / 2 < m h0)).trans_le (hmin hh)
    have hgap := (lt_div_iff₀ (hA z.2 hh)).mp hlt
    have hlow := mul_lt_mul_of_pos_left hz.1.1 (hA z.2 hh)
    have hupp := mul_lt_mul_of_pos_left hz.1.2 (hA z.2 hh)
    refine ⟨hz.2, ?_, ?_⟩ <;>
      dsimp only [phi, A] at hgap hlow hupp ⊢ <;> nlinarith only [hgap, hlow, hupp]
  have hclosed : Icc (0 : ℝ) 1 ×ˢ Icc (-2 * b) (2 * b) ⊆ U := by
    intro z hz
    exact hrect ⟨⟨by linarith only [hz.1.1, heta], by linarith only [hz.1.2, heta]⟩,
      ⟨by linarith only [hz.2.1, hb], by linarith only [hz.2.2, hb]⟩⟩
  have hreg (p : UnitTwoSphere) (hh : |f p| < 4 * b) (hq : 1 / (8 * a ^ 2) < q p) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
    have hhI : f p ∈ I := by simpa only [I, mem_Ioo, neg_mul] using abs_lt.mp hh
    have hy : (p : E3) 1 ≠ 0 := by
      intro hy
      have hp := (hpData p hhI hq).2.2.2.2.1
      rw [hy] at hp
      norm_num at hp
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, 0 < eps i * (p : E3) 1 := by
      rcases lt_or_gt_of_ne hy with hn | hp
      · exact ⟨1, by simpa only [eps, Matrix.cons_val_one, Matrix.cons_val_zero,
          neg_mul, one_mul] using neg_pos.mpr hn⟩
      · exact ⟨0, by simpa only [eps, Matrix.cons_val_zero, one_mul] using hp⟩
    have hp : p ∈ V i := ⟨hhI, hi, hq⟩
    have hs := hGmem i p hp
    have hident : f ∘ F i =ᶠ[𝓝 (G i p)] Prod.snd := by
      filter_upwards [hUopen.mem_nhds hs] with z hz
      exact (hFdata i z hz).1
    have hchain := mfderiv_comp (G i p) (hfm.mdifferentiable (by simp) (F i (G i p)))
      (((hFsm i).contMDiffAt (hUopen.mem_nhds hs)).mdifferentiableAt (by simp))
    change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (f ∘ F i) (G i p) : (ℝ × ℝ) →L[ℝ] ℝ) =
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (F i (G i p)) : E2 →L[ℝ] ℝ).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (F i) (G i p) : (ℝ × ℝ) →L[ℝ] E2) at hchain
    intro hzero
    have hsnd : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) Prod.snd (G i p) =
        ContinuousLinearMap.snd ℝ ℝ ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).mfderiv_eq
    have hbad := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (0, 1))
      (hident.mfderiv_eq.symm.trans hchain)
    rw [hsnd] at hbad
    change (1 : ℝ) = (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (F i (G i p)) : E2 →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (F i) (G i p) (0, 1)) at hbad
    have hz : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (F i (G i p)) = 0 :=
      (hFG i p hp).symm ▸ hzero
    rw [hz] at hbad
    change (1 : ℝ) = 0 at hbad
    exact one_ne_zero hbad
  have hwall (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) :
      (2 / a ^ 2 ≤ q (F i z) ↔ z.1 ∈ Icc (0 : ℝ) 1) ∧
      (2 / a ^ 2 < q (F i z) ↔ z.1 ∈ Ioo (0 : ℝ) 1) := by
    have hw := hWdata z hz
    have hh : z.2 ∈ Ht := ⟨hz.1.1.le, hz.1.2.le⟩
    have hrh := hr z.2 hh
    have hwr := hwR 1 ⟨by norm_num, by norm_num⟩
    have ht := htheta z.2 1 hh ⟨by norm_num, by norm_num⟩
    have htq := htheta z.2 (1 / 4) hh ⟨le_rfl, by norm_num⟩
    have hcos := hcosWindow (theta z.2 1) (phi z)
      ⟨ht.1, by linarith only [ht.2.1, Real.pi_pos]⟩
      ⟨by linarith only [htq.1, hz.2.1], by linarith only [htq.1, hz.2.2]⟩
    have hle : wR 1 ≤ W z ↔ Real.cos (phi z) ≤ Real.cos (theta z.2 1) := by
      rw [← hLm.le_iff_le hwr.2.2.1 hw.2.1, hwr.2.2.2.2.2, hw.2.2.1,
        ht.2.2, le_div_iff₀ hrh.1]
      constructor <;> intro h <;> nlinarith only [h]
    have hlt : wR 1 < W z ↔ Real.cos (phi z) < Real.cos (theta z.2 1) := by
      rw [← hLm.lt_iff_lt hwr.2.2.1 hw.2.1, hwr.2.2.2.2.2, hw.2.2.1,
        ht.2.2, lt_div_iff₀ hrh.1]
      constructor <;> intro h <;> nlinarith only [h]
    have hphiLe : phi z ∈ Icc (theta z.2 1) (2 * Real.pi - theta z.2 1) ↔
        z.1 ∈ Icc (0 : ℝ) 1 := by
      have ha := hA z.2 hh
      constructor <;> intro h <;> constructor <;>
        dsimp only [mem_Icc, phi, A] at h ha ⊢ <;> nlinarith only [h.1, h.2, ha]
    have hphiLt : phi z ∈ Ioo (theta z.2 1) (2 * Real.pi - theta z.2 1) ↔
        z.1 ∈ Ioo (0 : ℝ) 1 := by
      have ha := hA z.2 hh
      constructor <;> intro h <;> constructor <;>
        dsimp only [mem_Ioo, phi, A] at h ha ⊢ <;> nlinarith only [h.1, h.2, ha]
    rw [(hFdata i z hz).2.1]
    have hc := hqCompare 1 (W z) ⟨by norm_num, by norm_num⟩ hw.1
    norm_num only [one_pow, mul_one] at hc
    exact ⟨hc.1.trans (by simpa only [wR, one_pow, mul_one] using hle.trans (hcos.2.trans hphiLe)),
      hc.2.trans (by simpa only [wR, one_pow, mul_one] using hlt.trans (hcos.1.trans hphiLt))⟩
  refine ⟨eta, Q, heta, hetasmall, fun i =>
    ⟨rfl, rfl, hFsm i, hGsm i, hFcoe i, fun _ _ => rfl,
      fun z hz => (hFdata i z hz).1⟩, hrect, hclosed, hreg,
    fun i h t hz => hwall i (t, h) hz, ?_⟩
  intro i h hh R hR
  let tR : ℝ := (theta h R - theta h 1) / A h
  have hhT : h ∈ Ht := ⟨hh.1.le, hh.2.le⟩
  have hRT : R ∈ Rt := ⟨by linarith only [hR.1], hR.2.le⟩
  have haA := (hA h hhT).ne'
  have ht := htheta h R hhT hRT
  have htq := htheta h (1 / 4) hhT ⟨le_rfl, by norm_num⟩
  have hrh := hr h hhT
  have hwr := hwR R hRT
  have hgap : theta h (1 / 4) < theta h R :=
    hthetaMono h hhT ⟨le_rfl, by norm_num⟩ hRT (by linarith only [hR.1])
  have hph0 : phi (tR, h) = theta h R := by dsimp only [phi, tR]; field_simp; ring
  have hph1 : phi (1 - tR, h) = 2 * Real.pi - theta h R := by
    dsimp only [phi, tR]
    field_simp
    dsimp only [A]
    ring
  have hs0 : (tR, h) ∈ U := by
    change h ∈ I ∧ theta h (1 / 4) < phi (tR, h) ∧
      phi (tR, h) < 2 * Real.pi - theta h (1 / 4)
    rw [hph0]
    exact ⟨hh, hgap, by linarith only [ht.2.1, htq.2.1, Real.pi_pos]⟩
  have hs1 : (1 - tR, h) ∈ U := by
    change h ∈ I ∧ theta h (1 / 4) < phi (1 - tR, h) ∧
      phi (1 - tR, h) < 2 * Real.pi - theta h (1 / 4)
    rw [hph1]
    exact ⟨hh, by linarith only [ht.2.1, htq.2.1, Real.pi_pos], by linarith only [hgap]⟩
  have hcosr : r h * Real.cos (theta h R) = Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) := by
    rw [ht.2.2]
    field_simp [hrh.1.ne']
  have harg : -r h * Real.cos (theta h R) = L (wR R) := by
    rw [hwr.2.2.2.2.2]
    linarith only [hcosr]
  have hWrad (s : ℝ) (hs : Real.cos (phi (s, h)) = Real.cos (theta h R)) : W (s, h) = wR R := by
    change L.symm (-r h * Real.cos (phi (s, h))) = _
    rw [hs, harg]
    exact L.left_inv hwr.2.2.1
  have hw0 := hWrad tR (by rw [hph0])
  have hw1 := hWrad (1 - tR) (by rw [hph1, Real.cos_two_pi_sub])
  have hxs : (r h * Real.sin (theta h R)) ^ 2 = R ^ 2 / a ^ 2 + h := by
    have hc := congrArg (fun x : ℝ => x ^ 2) hcosr
    have hs := Real.sq_sqrt (by linarith only [(hscale R hRT).2.1] :
      0 ≤ 1 / 4 - R ^ 2 / a ^ 2)
    have htr := congrArg (fun x : ℝ => (r h) ^ 2 * x) (Real.sin_sq_add_cos_sq (theta h R))
    nlinarith only [hc, hs, htr, hrh.2.1]
  have hx : r h * Real.sin (theta h R) = Real.sqrt (R ^ 2 / a ^ 2 + h) := by
    rw [← hxs, Real.sqrt_sq (mul_pos hrh.1
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2.1, Real.pi_pos]))).le]
  have hEs (s : ℝ) (hw : W (s, h) = wR R)
      (hs : (r h * Real.sin (phi (s, h))) ^ 2 = R ^ 2 / a ^ 2 + h) :
      energy (s, h) = R ^ 2 / a ^ 2 - h := by
    change 1 - (r h) ^ 2 * Real.sin (phi (s, h)) ^ 2 - (W (s, h)) ^ 2 = _
    rw [← mul_pow, hs, hw]
    have hw2 : (wR R) ^ 2 = 1 - 2 * R ^ 2 / a ^ 2 := by
      dsimp only [wR]
      rw [neg_sq, Real.sq_sqrt (by linarith only [(hscale R hRT).2.2.1, hsigmaSmall])]
    rw [hw2]
    ring
  have he0 := hEs tR hw0 (by rw [hph0]; exact hxs)
  have he1 := hEs (1 - tR) hw1 (by rw [hph1, Real.sin_two_pi_sub, mul_neg, neg_sq]; exact hxs)
  refine ⟨hs0, hs1, ?_, ?_⟩
  · change (F i (tR, h) : E3) = _
    rw [hFcoe i (tR, h) hs0]
    dsimp only [T]
    rw [hph0, hw0, he0]
    simp only [mul_assoc, hx, wR, eps]
  · change (F i (1 - tR, h) : E3) = _
    rw [hFcoe i (1 - tR, h) hs1]
    dsimp only [T]
    rw [hph1, hw1, he1, Real.sin_two_pi_sub]
    simp only [mul_neg, mul_assoc, hx, neg_mul, wR, eps]

end PoincareConjecture.M25.Topology3D
