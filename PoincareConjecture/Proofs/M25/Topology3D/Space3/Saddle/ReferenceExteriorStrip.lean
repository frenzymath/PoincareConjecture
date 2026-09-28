import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceExteriorCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.EndpointReparametrization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_exterior_strip
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
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
    let B0 := nonnestedReferenceBallChart 0 d hd
    let port : Fin 4 → E2 :=
      ![J2.symm (1 / Real.sqrt 2, 1 / Real.sqrt 2),
        J2.symm (-1 / Real.sqrt 2, 1 / Real.sqrt 2),
        J2.symm (-1 / Real.sqrt 2, -1 / Real.sqrt 2),
        J2.symm (1 / Real.sqrt 2, -1 / Real.sqrt 2)]
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let p0 : E2 → E3 := fun x =>
      !₂[Real.sqrt 2 * (J2 x).1 / a, Real.sqrt 2 * (J2 x).2 / a,
        -1 + 2 * (J2 x).2 ^ 2 / a ^ 2 - d (2 * ‖x‖ ^ 2 / a ^ 2)]
    ∃ (eta : ℝ) (Q : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere),
    let M : Fin 2 → ℝ → ℝ → E2 := fun i h t =>
      a • J2.symm ((Q i (t, h) : E3) 0 / Real.sqrt 2,
        (Q i (t, h) : E3) 1 / Real.sqrt 2)
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
      (∀ z ∈ U, f (Q i z) = z.2) ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => M i z.2 z.1)
        (Ioo (-eta) (1 + eta) ×ˢ I)) ∧
    Ioo (-eta) (1 + eta) ×ˢ I ⊆ U ∧
    Icc (0 : ℝ) 1 ×ˢ Icc (-2 * b) (2 * b) ⊆ U ∧
    (∀ p : UnitTwoSphere, |f p| < 4 * b → 1 / (8 * a ^ 2) < q p →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0) ∧
    (∀ h ∈ I,
      (∀ i : Fin 2,
        ContDiffOn ℝ ∞ (M i h) (Ioo (-eta) (1 + eta)) ∧
        InjOn (M i h) (Ioo (-eta) (1 + eta)) ∧
        (∀ t ∈ Ioo (-eta) (1 + eta), deriv (M i h) t ≠ 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, 0 < eps i * (J2 (M i h t)).2) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 1 < ‖M i h t‖)) ∧
      Disjoint (M 0 h '' Icc (0 : ℝ) 1) (M 1 h '' Icc (0 : ℝ) 1) ∧
      (⋃ i : Fin 2, M i h '' Icc (0 : ℝ) 1) =
        {x : E2 | 1 ≤ ‖x‖ ∧ (((J2 x).1 / a, (J2 x).2 / a), h) ∈ B0.boundary}) ∧
    (∀ (i : Fin 2) (h : ℝ), h ∈ I → ∀ R ∈ Ioo (7 / 8 : ℝ) (9 / 8),
      let tR : ℝ := (theta h R - theta h 1) / A h
      (tR, h) ∈ U ∧ (1 - tR, h) ∈ U ∧
      M i h tR = J2.symm
        (eps i * Real.sqrt ((R ^ 2 + a ^ 2 * h) / 2),
          eps i * Real.sqrt ((R ^ 2 - a ^ 2 * h) / 2)) ∧
      M i h (1 - tR) = J2.symm
        (-eps i * Real.sqrt ((R ^ 2 + a ^ 2 * h) / 2),
          eps i * Real.sqrt ((R ^ 2 - a ^ 2 * h) / 2))) ∧
    ∃ (nu : ℝ) (Theta : Fin 2 → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞),
    let alpha : Fin 2 → ℝ → E2 := fun i t => M i 0 (Theta i t)
    0 < nu ∧ nu < eta / 8 ∧
    (∀ i : Fin 2,
      StrictMono (Theta i) ∧ StrictMono (Theta i).symm ∧
      (∀ t : ℝ, 0 < deriv (Theta i) t) ∧ Theta i 0 = 0 ∧ Theta i 1 = 1 ∧
      Theta i '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 ∧
      MapsTo (Theta i) (Icc (-nu) (1 + nu)) (Ioo (-eta) (1 + eta)) ∧
      ContDiffOn ℝ ∞ (alpha i) (Ioo (-nu) (1 + nu)) ∧
      InjOn (alpha i) (Ioo (-nu) (1 + nu)) ∧
      (∀ t ∈ Ioo (-nu) (1 + nu), deriv (alpha i) t ≠ 0) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 < eps i * (J2 (alpha i t)).2) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, 1 < ‖alpha i t‖) ∧
      (∀ t : ℝ, |t| < nu → alpha i t = (1 + t) • port (ep (i, 0))) ∧
      (∀ t : ℝ, |t - 1| < nu → alpha i t = (2 - t) • port (ep (i, 1)))) ∧
    Disjoint (alpha 0 '' Icc (0 : ℝ) 1) (alpha 1 '' Icc (0 : ℝ) 1) ∧
    (⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1) =
      {x : E2 | 1 ≤ ‖x‖ ∧ (((J2 x).1 / a, (J2 x).2 / a), 0) ∈ B0.boundary} ∧
    (∀ (i : Fin 2) (x : E2), x ∈ alpha i '' Ioo (-nu) (1 + nu) →
      ∃ hx : p0 x ∈ sphere (0 : E3) 1,
        let p : UnitTwoSphere := ⟨p0 x, hx⟩
        let s : ℝ := (P i p - theta 0 1) / A 0
        p ∈ V i ∧ (Q i).symm p = (s, 0) ∧
        (Theta i).symm s ∈ Ioo (-nu) (1 + nu) ∧
        alpha i ((Theta i).symm s) = x) := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
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
  let B0 := nonnestedReferenceBallChart 0 d hd
  let port : Fin 4 → E2 :=
    ![J2.symm (1 / Real.sqrt 2, 1 / Real.sqrt 2),
      J2.symm (-1 / Real.sqrt 2, 1 / Real.sqrt 2),
      J2.symm (-1 / Real.sqrt 2, -1 / Real.sqrt 2),
      J2.symm (1 / Real.sqrt 2, -1 / Real.sqrt 2)]
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let p0 : E2 → E3 := fun x =>
    !₂[Real.sqrt 2 * (J2 x).1 / a, Real.sqrt 2 * (J2 x).2 / a,
      -1 + 2 * (J2 x).2 ^ 2 / a ^ 2 - d (2 * ‖x‖ ^ 2 / a ^ 2)]
  obtain ⟨eta0, Q, heta0, heta0Small, hQ, hrect0, hclosed, hreg, hwall, hrad⟩ :=
    exists_nonnested_reference_exterior_coordinates sigma hsigma hsigmaSmall
      d hd hdNear hdZero hdBounds hdDeriv a ha haCorrection haLarge
  let M : Fin 2 → ℝ → ℝ → E2 := fun i h t =>
    a • J2.symm ((Q i (t, h) : E3) 0 / Real.sqrt 2,
      (Q i (t, h) : E3) 1 / Real.sqrt 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hzero : (0 : ℝ) ∈ I := ⟨by linarith only [hb], by linarith only [hb]⟩
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let N := nonnestedReferenceDiffeomorph 0 d hd
  let lift : ℝ → E2 → (ℝ × ℝ) × ℝ := fun h x =>
    (((J2 x).1 / a, (J2 x).2 / a), h)
  have hQs (i : Fin 2) : (Q i).source = U := (hQ i).1
  have hQt (i : Fin 2) : (Q i).target = V i := (hQ i).2.1
  have hQheight (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : f (Q i z) = z.2 :=
    (hQ i).2.2.2.2.2.2 z hz
  have hQtarget (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) : Q i z ∈ V i := by
    rw [← hQt]
    exact (Q i).map_source (by rwa [hQs])
  have hJM (i : Fin 2) (h t : ℝ) : J2 (M i h t) =
      (a * (Q i (t, h) : E3) 0 / Real.sqrt 2,
        a * (Q i (t, h) : E3) 1 / Real.sqrt 2) := by
    simp only [M, map_smul, ContinuousLinearEquiv.apply_symm_apply,
      Prod.smul_mk, smul_eq_mul, mul_div_assoc]
  have hN (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) :
      N (Q i z : E3) = lift z.2 (M i z.2 z.1) := by
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
    dsimp only [lift]
    rw [hJM]
    apply Prod.ext
    · apply Prod.ext <;> dsimp <;> field_simp [ha.ne']
    · simpa only [zero_add] using hQheight i z hz
  have hMnorm (i : Fin 2) (h t : ℝ) :
      ‖M i h t‖ ^ 2 = a ^ 2 / 2 * q (Q i (t, h)) := by
    rw [← hJ2, hJM]
    dsimp only [q]
    simp only [div_pow, mul_pow, hsqrt2]
    ring
  have hMbound (i : Fin 2) (z : ℝ × ℝ) (hz : z ∈ U) :
      lift z.2 (M i z.2 z.1) ∈ B0.boundary := by
    change lift z.2 (M i z.2 z.1) ∈ N '' sphere (0 : E3) 1
    exact ⟨Q i z, (Q i z).property, hN i z hz⟩
  have hUopen : IsOpen U := by rw [← hQs 0]; exact (Q 0).open_source
  have hMsm (i : Fin 2) :
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => M i z.2 z.1) U := by
    have hc := contMDiff_coe_sphere.comp_contMDiffOn (hQ i).2.2.1
    have hd0 : ContDiffOn ℝ ∞ (fun z => (Q i z : E3) 0) U :=
      (contDiff_piLp_apply 2).comp_contDiffOn hc.contDiffOn
    have hd1 : ContDiffOn ℝ ∞ (fun z => (Q i z : E3) 1) U :=
      (contDiff_piLp_apply 2).comp_contDiffOn hc.contDiffOn
    exact (contDiffOn_const (c := a)).smul (J2.symm.contDiff.comp_contDiffOn
      ((hd0.div_const _).prodMk (hd1.div_const _)))
  have hMt (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) : ContDiffAt ℝ ∞ (M i h) t := by
    have hs : ContDiffAt ℝ ∞ (fun s : ℝ => (s, h)) t :=
      contDiffAt_id.prodMk contDiffAt_const
    have hc := ((hMsm i).contDiffAt (hUopen.mem_nhds ht)).comp t hs
    exact hc
  have hLift (h : ℝ) : ContDiff ℝ ∞ (lift h) :=
    ((J2.contDiff.fst.div_const a).prodMk (J2.contDiff.snd.div_const a)).prodMk
      contDiff_const
  let R : Fin 2 → ℝ → E2 → ℝ := fun i h x =>
    ((Q i).symm (sphereDirection (N.symm (lift h x)))).1
  have hRM (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) : R i h (M i h t) = t := by
    have hn : N.symm (lift h (M i h t)) = (Q i (t, h) : E3) := by
      rw [← hN i (t, h) ht, N.symm_apply_apply]
    have hs : sphereDirection (Q i (t, h) : E3) = Q i (t, h) := by
      simpa only [one_smul] using sphereDirection_smul (Q i (t, h)) zero_lt_one
    dsimp only [R]
    rw [hn, hs, (Q i).left_inv (by rwa [hQs])]
  have hRsm (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) :
      ContDiffAt ℝ ∞ (R i h) (M i h t) := by
    have hn : N.symm (lift h (M i h t)) = (Q i (t, h) : E3) := by
      rw [← hN i (t, h) ht, N.symm_apply_apply]
    have hs : sphereDirection (N.symm (lift h (M i h t))) = Q i (t, h) := by
      rw [hn]
      simpa only [one_smul] using sphereDirection_smul (Q i (t, h)) zero_lt_one
    have hdir := sphereDirection_contMDiffOn.contMDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds (show N.symm (lift h (M i h t)) ≠ 0 by
        rw [hn]; exact ne_zero_of_mem_unit_sphere _))
    have hi : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (Q i).symm
        (sphereDirection (N.symm (lift h (M i h t)))) :=
      (hQ i).2.2.2.1.contMDiffAt (by
        change V i ∈ 𝓝 (sphereDirection (N.symm (lift h (M i h t))))
        rw [hs, ← hQt]
        exact (Q i).open_target.mem_nhds (by rw [hQt]; exact hQtarget i (t, h) ht))
    have hnsm := N.symm.contMDiff.contMDiffAt.comp (M i h t)
      (hLift h).contDiffAt.contMDiffAt
    have hpair := hi.comp (M i h t) (hdir.comp (M i h t) hnsm)
    have hc := contDiffAt_fst.contMDiffAt.comp (M i h t) hpair
    exact hc.contDiffAt
  have hMinj (i : Fin 2) (h : ℝ) : InjOn (M i h) {t | (t, h) ∈ U} := by
    intro s hs t ht he
    exact (hRM i h s hs).symm.trans ((congrArg (R i h) he).trans (hRM i h t ht))
  have hMderiv (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) : deriv (M i h) t ≠ 0 := by
    have heq : R i h ∘ M i h =ᶠ[𝓝 t] id := by
      filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hUopen.mem_nhds ht)] with s hs
      exact hRM i h s hs
    have hc := ((hRsm i h t ht).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hMt i h t ht).differentiableAt (by simp)).hasDerivAt
    have hd : fderiv ℝ (R i h) (M i h t) (deriv (M i h) t) = 1 := by
      simpa only [deriv_id] using hc.deriv.symm.trans heq.deriv_eq
    intro hz
    rw [hz, map_zero] at hd
    exact zero_ne_one hd
  have hsign (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) :
      0 < eps i * (J2 (M i h t)).2 := by
    rw [hJM]
    have hp := (hQtarget i (t, h) ht).2.1
    change 0 < eps i * (a * (Q i (t, h) : E3) 1 / Real.sqrt 2)
    have he : eps i * (a * (Q i (t, h) : E3) 1 / Real.sqrt 2) =
        a / Real.sqrt 2 * (eps i * (Q i (t, h) : E3) 1) := by ring
    rw [he]
    exact mul_pos (div_pos ha hsqrt) hp
  have hMne (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) : M i h t ≠ 0 := by
    intro he
    have hs := hsign i h t ht
    rw [he, map_zero] at hs
    simp at hs
  have hnormWall (i : Fin 2) (h t : ℝ) (ht : (t, h) ∈ U) :
      (1 ≤ ‖M i h t‖ ↔ t ∈ Icc (0 : ℝ) 1) ∧
      (1 < ‖M i h t‖ ↔ t ∈ Ioo (0 : ℝ) 1) := by
    have hn := hMnorm i h t
    have hd : a ^ 2 / 2 * (2 / a ^ 2) = 1 := by field_simp
    have hw := hwall i h t ht
    have hc : 0 < a ^ 2 / 2 := by positivity
    have he : 2 / a ^ 2 ≤ q (Q i (t, h)) ↔ 1 ≤ ‖M i h t‖ := by
      rw [← mul_le_mul_iff_right₀ hc, hd, ← hn]
      constructor <;> intro hx <;> nlinarith only [hx, norm_nonneg (M i h t)]
    have hl : 2 / a ^ 2 < q (Q i (t, h)) ↔ 1 < ‖M i h t‖ := by
      rw [← mul_lt_mul_iff_right₀ hc, hd, ← hn]
      constructor <;> intro hx <;> nlinarith only [hx, norm_nonneg (M i h t)]
    exact ⟨he.symm.trans hw.1, hl.symm.trans hw.2⟩
  have hdisjoint (h : ℝ) (hh : h ∈ I) :
      Disjoint (M 0 h '' Icc (0 : ℝ) 1) (M 1 h '' Icc (0 : ℝ) 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    have h0 := hsign 0 h s (hrect0 ⟨⟨by linarith only [heta0, hs.1],
      by linarith only [heta0, hs.2]⟩, hh⟩)
    have h1 := hsign 1 h t (hrect0 ⟨⟨by linarith only [heta0, ht.1],
      by linarith only [heta0, ht.2]⟩, hh⟩)
    rw [he] at h1
    norm_num only [eps, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, neg_mul] at h0 h1
    linarith only [h0, h1]
  have hcover (h : ℝ) (hh : h ∈ I) :
      (⋃ i : Fin 2, M i h '' Icc (0 : ℝ) 1) =
        {x : E2 | 1 ≤ ‖x‖ ∧ lift h x ∈ B0.boundary} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hx
      have hs : (t, h) ∈ U := hrect0 ⟨⟨by linarith only [heta0, ht.1],
        by linarith only [heta0, ht.2]⟩, hh⟩
      exact ⟨(hnormWall i h t hs).1.mpr ht, hMbound i (t, h) hs⟩
    · rintro ⟨hx, hp⟩
      change lift h x ∈ N '' sphere (0 : E3) 1 at hp
      obtain ⟨y, hy, he⟩ := hp
      let p : UnitTwoSphere := ⟨y, hy⟩
      have hf : f p = h := by
        have hz := congrArg Prod.snd he
        simpa only [N, nonnestedReferenceDiffeomorph_apply_symm,
          lift, f, zero_add] using hz
      have hxy : y 0 = Real.sqrt 2 * (J2 x).1 / a ∧
          y 1 = Real.sqrt 2 * (J2 x).2 / a := by
        have h0 := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) he
        have h1 := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2) he
        change y 0 / Real.sqrt 2 = (J2 x).1 / a at h0
        change y 1 / Real.sqrt 2 = (J2 x).2 / a at h1
        constructor
        · calc
            y 0 = (y 0 / Real.sqrt 2) * Real.sqrt 2 :=
              (div_mul_cancel₀ _ hsqrt.ne').symm
            _ = Real.sqrt 2 * (J2 x).1 / a := by rw [h0]; ring
        · calc
            y 1 = (y 1 / Real.sqrt 2) * Real.sqrt 2 :=
              (div_mul_cancel₀ _ hsqrt.ne').symm
            _ = Real.sqrt 2 * (J2 x).2 / a := by rw [h1]; ring
      have hqp : q p = 2 * ‖x‖ ^ 2 / a ^ 2 := by
        dsimp only [q, p]
        rw [hxy.1, hxy.2, div_pow, div_pow, mul_pow, mul_pow, hsqrt2]
        rw [← hJ2]
        ring
      have hlarge : 2 / a ^ 2 ≤ q p := by
        rw [hqp, div_le_div_iff_of_pos_right ha2]
        nlinarith only [hx]
      have hq0 : 0 ≤ q p := by dsimp only [q]; positivity
      have hsum : q p + (y 2) ^ 2 = 1 := by
        have hn := EuclideanSpace.real_norm_sq_eq y
        rw [mem_sphere_zero_iff_norm.mp hy, Fin.sum_univ_three] at hn
        simpa only [q, p, one_pow] using hn.symm
      have hyne : y 1 ≠ 0 := by
        intro hy0
        have hf' : h = 1 + y 2 + d (q p) := by
          rw [← hf]
          change 1 + y 2 - (y 1) ^ 2 + d (q p) = _
          rw [hy0]
          ring
        have hqle : q p ≤ 2 * (1 + y 2) := by
          nlinarith only [hsum, sq_nonneg (y 2 + 1)]
        have hhi : h < 1 / (32 * a ^ 2) := by
          have heq : 4 * b = 1 / (32 * a ^ 2) := by dsimp only [b]; ring
          exact hh.2.trans_eq heq
        have hqbig : 0 < 2 / a ^ 2 := by positivity
        have hfrac : 2 / a ^ 2 = 64 * (1 / (32 * a ^ 2)) := by ring
        by_cases hsmall : sigma ≤ q p
        · rw [hdZero _ hsmall] at hf'
          nlinarith only [hf', hqle, hhi, hlarge, hfrac, hqbig]
        · have hqs : q p ≤ 1 / 16 := (lt_of_not_ge hsmall).le.trans hsigmaSmall
          have hdq := (hdBounds _ hq0).1
          have hsq : (q p) ^ 2 ≤ q p / 16 := by
            nlinarith only [mul_nonneg hq0 (sub_nonneg.mpr hqs)]
          nlinarith only [hf', hqle, hhi, hlarge, hfrac, hqbig, hdq, hsq]
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, 0 < eps i * y 1 := by
        rcases lt_or_gt_of_ne hyne with hn | hp
        · exact ⟨1, by norm_num [eps]; linarith only [hn]⟩
        · exact ⟨0, by simpa [eps] using hp⟩
      have hv : p ∈ V i := ⟨by rwa [hf], hi, by
        have hgap : 1 / (8 * a ^ 2) < 2 / a ^ 2 := by
          field_simp
          nlinarith only [ha2]
        exact hgap.trans_le hlarge⟩
      let z := (Q i).symm p
      have hz : z ∈ U := by rw [← hQs]; exact (Q i).map_target (by rwa [hQt])
      have hqz : Q i z = p := (Q i).right_inv (by rwa [hQt])
      have hzh : z.2 = h := by rw [← hQheight i z hz, hqz, hf]
      have ht : z.1 ∈ Icc (0 : ℝ) 1 :=
        (hwall i z.2 z.1 hz).1.mp (by simpa only [Prod.mk.eta, hqz] using hlarge)
      apply mem_iUnion.mpr
      refine ⟨i, z.1, ht, ?_⟩
      apply J2.injective
      rw [← hzh, hJM]
      change (a * (Q i z : E3) 0 / Real.sqrt 2,
        a * (Q i z : E3) 1 / Real.sqrt 2) = J2 x
      rw [hqz]
      apply Prod.ext <;> dsimp only [p] <;> simp only [hxy.1, hxy.2] <;>
        field_simp [ha.ne', hsqrt.ne']
  have hroot (x : ℝ) : a * Real.sqrt x / Real.sqrt 2 = Real.sqrt (a ^ 2 * x / 2) := by
    rw [show a ^ 2 * x / 2 = (a ^ 2 / 2) * x by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_div (sq_nonneg a), Real.sqrt_sq ha.le]
    ring
  have hradM (i : Fin 2) (h : ℝ) (hh : h ∈ I) (R : ℝ)
      (hR : R ∈ Ioo (7 / 8 : ℝ) (9 / 8)) :
      let tR : ℝ := (theta h R - theta h 1) / A h
      (tR, h) ∈ U ∧ (1 - tR, h) ∈ U ∧
      M i h tR = J2.symm
        (eps i * Real.sqrt ((R ^ 2 + a ^ 2 * h) / 2),
          eps i * Real.sqrt ((R ^ 2 - a ^ 2 * h) / 2)) ∧
      M i h (1 - tR) = J2.symm
        (-eps i * Real.sqrt ((R ^ 2 + a ^ 2 * h) / 2),
          eps i * Real.sqrt ((R ^ 2 - a ^ 2 * h) / 2)) := by
    obtain ⟨hs0, hs1, he0, he1⟩ := hrad i h hh R hR
    have hp : a * Real.sqrt (R ^ 2 / a ^ 2 + h) / Real.sqrt 2 =
        Real.sqrt ((R ^ 2 + a ^ 2 * h) / 2) := by
      rw [hroot]
      congr 1
      field_simp
    have hm : a * Real.sqrt (R ^ 2 / a ^ 2 - h) / Real.sqrt 2 =
        Real.sqrt ((R ^ 2 - a ^ 2 * h) / 2) := by
      rw [hroot]
      congr 1
      field_simp
    refine ⟨hs0, hs1, ?_, ?_⟩ <;> apply J2.injective <;>
      rw [hJM, ContinuousLinearEquiv.apply_symm_apply]
    · rw [he0]
      change (a * (eps i * Real.sqrt (R ^ 2 / a ^ 2 + h)) / Real.sqrt 2,
        a * (eps i * Real.sqrt (R ^ 2 / a ^ 2 - h)) / Real.sqrt 2) = _
      simp only [show ∀ e x : ℝ, a * (e * x) / Real.sqrt 2 =
        e * (a * x / Real.sqrt 2) by intros; ring, hp, hm]
    · rw [he1]
      change (a * (-eps i * Real.sqrt (R ^ 2 / a ^ 2 + h)) / Real.sqrt 2,
        a * (eps i * Real.sqrt (R ^ 2 / a ^ 2 - h)) / Real.sqrt 2) = _
      simp only [show ∀ e x : ℝ, a * (e * x) / Real.sqrt 2 =
        e * (a * x / Real.sqrt 2) by intros; ring, hp, hm]
  have hport (i k : Fin 2) : M i 0 (k : ℝ) = port (ep (i, k)) := by
    have hrad1 := hradM i 0 hzero 1 ⟨by norm_num, by norm_num⟩
    simp only [sub_self, zero_div, sub_zero, one_pow, mul_zero, add_zero] at hrad1
    have hs : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
      rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    fin_cases k
    · fin_cases i <;> simpa [port, ep, finProdFinEquiv, eps, hs, neg_div] using hrad1.2.2.1
    · fin_cases i <;> simpa [port, ep, finProdFinEquiv, eps, hs, neg_div] using hrad1.2.2.2
  have hportNorm (j : Fin 4) : ‖port j‖ = 1 := by
    have hn : ‖port j‖ ^ 2 = 1 := by
      rw [← hJ2]
      fin_cases j <;> norm_num [port, div_pow, hsqrt2]
    nlinarith only [hn, norm_nonneg (port j)]
  have hPortJ (i k : Fin 2) : J2 (port (ep (i, k))) =
      (eps k * eps i / Real.sqrt 2, eps i / Real.sqrt 2) := by
    fin_cases i <;> fin_cases k <;> simp [port, ep, finProdFinEquiv, eps]
  have heps (i : Fin 2) : (eps i) ^ 2 = 1 := by fin_cases i <;> norm_num [eps]
  have hkU (k : Fin 2) : ((k : ℝ), 0) ∈ U := by
    apply hrect0
    refine ⟨?_, hzero⟩
    fin_cases k <;> norm_num <;> constructor <;> linarith only [heta0]
  have hRay (i k : Fin 2) (t : ℝ) (ht : (t, 0) ∈ U)
      (hn : ‖M i 0 t‖ < 9 / 8)
      (hx : 0 < eps k * eps i * (J2 (M i 0 t)).1) :
      M i 0 t = ‖M i 0 t‖ • port (ep (i, k)) := by
    let x := M i 0 t
    have haσ : 16 < a ^ 2 * sigma := (div_lt_iff₀ hsigma).mp haCorrection
    have hbox : (J2 x).1 ^ 2 / a ^ 2 + (J2 x).2 ^ 2 / a ^ 2 < sigma / 4 := by
      rw [← add_div, hJ2, div_lt_iff₀ ha2]
      nlinarith only [hn, norm_nonneg x, haσ]
    have hbnd := (nonnestedReferenceBallChart_morse_box 0 d hd sigma hsigma hsigmaSmall
      hdNear (lift 0 x) (by simpa only [lift, div_pow] using hbox) (by norm_num)).2.2.mp
        (hMbound i (t, 0) ht)
    have hsq : (J2 x).1 ^ 2 = (J2 x).2 ^ 2 := by
      change 0 = 0 + ((J2 x).1 / a) ^ 2 - ((J2 x).2 / a) ^ 2 at hbnd
      field_simp at hbnd
      linarith only [hbnd]
    have hscalar (s y : ℝ) (hs : s ^ 2 = 1) (hy : 0 < s * y)
        (hy2 : 2 * y ^ 2 = ‖x‖ ^ 2) : y = s * ‖x‖ / Real.sqrt 2 := by
      have hh : (s * y) ^ 2 = (‖x‖ / Real.sqrt 2) ^ 2 := by
        rw [mul_pow, hs, one_mul, div_pow, hsqrt2]
        linarith only [hy2]
      have he := (sq_eq_sq₀ hy.le (div_nonneg (norm_nonneg x) hsqrt.le)).mp hh
      calc
        y = s * (s * y) := by nlinarith only [congrArg (fun z : ℝ => z * y) hs]
        _ = s * ‖x‖ / Real.sqrt 2 := by rw [he]; ring
    have h1 := hscalar (eps k * eps i) (J2 x).1 (by rw [mul_pow, heps, heps, mul_one])
      hx (by linarith only [hJ2 x, hsq])
    have h2 := hscalar (eps i) (J2 x).2 (heps i) (hsign i 0 t ht)
      (by linarith only [hJ2 x, hsq])
    apply J2.injective
    change J2 x = J2 (‖x‖ • port (ep (i, k)))
    rw [show J2 (‖x‖ • port (ep (i, k))) = ‖x‖ • J2 (port (ep (i, k))) from
      J2.map_smul _ _, hPortJ]
    apply Prod.ext <;> dsimp only [Prod.smul_mk, smul_eq_mul] <;>
      simp only [h1, h2] <;> ring
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i k : Fin 2,
      (((k : ℝ) + s), 0) ∈ U ∧ ‖M i 0 ((k : ℝ) + s)‖ < 9 / 8 ∧
        0 < eps k * eps i * (J2 (M i 0 ((k : ℝ) + s))).1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro k
    have hc := (hMt i 0 k (hkU k)).continuousAt
    have hsign0 : 0 < eps k * eps i * (J2 (M i 0 k)).1 := by
      rw [hport, hPortJ]
      have he : eps k * eps i * (eps k * eps i / Real.sqrt 2) = 1 / Real.sqrt 2 := by
        calc
          _ = (eps k) ^ 2 * (eps i) ^ 2 / Real.sqrt 2 := by ring
          _ = _ := by rw [heps, heps, one_mul]
      rw [he]
      positivity
    have hn : ‖M i 0 (k : ℝ)‖ < 9 / 8 := by rw [hport, hportNorm]; norm_num
    have he : ∀ᶠ t in 𝓝 (k : ℝ), (t, 0) ∈ U ∧ ‖M i 0 t‖ < 9 / 8 ∧
        0 < eps k * eps i * (J2 (M i 0 t)).1 := by
      filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hUopen.mem_nhds (hkU k)), hc.norm.eventually_lt continuousAt_const hn,
        continuousAt_const.eventually_lt
          (continuousAt_const.mul (J2.continuous.continuousAt.comp hc).fst) hsign0] with t ht hn hs
      exact ⟨ht, hn, hs⟩
    have hshift : Tendsto (fun s : ℝ => (k : ℝ) + s) (𝓝 0) (𝓝 (k : ℝ)) := by
      have hc : ContinuousAt (fun s : ℝ => (k : ℝ) + s) 0 :=
        continuousAt_const.add continuousAt_id
      simpa only [add_zero] using hc.tendsto
    exact hshift.eventually he
  obtain ⟨delta, hdelta, hdeltaBall⟩ := Metric.eventually_nhds_iff.mp hnear
  let eta := min eta0 delta / 2
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have heta0 : eta < eta0 := by dsimp only [eta]; linarith only [min_le_left eta0 delta, heta0]
  have hetad : eta < delta := by dsimp only [eta]; linarith only [min_le_right eta0 delta, hdelta]
  have hrect : Ioo (-eta) (1 + eta) ×ˢ I ⊆ U := by
    intro z hz
    exact hrect0 ⟨⟨by linarith only [hz.1.1, heta0],
      by linarith only [hz.1.2, heta0]⟩, hz.2⟩
  have hEnd (i k : Fin 2) (t : ℝ) (ht : |t - (k : ℝ)| < eta) :
      (t, 0) ∈ U ∧ M i 0 t = ‖M i 0 t‖ • port (ep (i, k)) := by
    have he := hdeltaBall (y := t - (k : ℝ)) (by
      simpa only [Real.dist_eq, sub_zero] using ht.trans hetad) i k
    rw [show (k : ℝ) + (t - (k : ℝ)) = t by ring] at he
    exact ⟨he.1, hRay i k t he.1 he.2.1 he.2.2⟩
  have hNormsm (i : Fin 2) (t : ℝ) (ht : (t, 0) ∈ U) :
      ContDiffAt ℝ ∞ (fun s => ‖M i 0 s‖) t := (hMt i 0 t ht).norm ℝ (hMne i 0 t ht)
  have hRadialDeriv (i k : Fin 2) : 0 < eps k * deriv (fun t => ‖M i 0 t‖) k := by
    have hb0 : (0 : ℝ) ∈ Icc (-4 * b) (4 * b) := ⟨hzero.1.le, hzero.2.le⟩
    have hscalar := nonnested_reference_exterior_scalar_bounds sigma hsigma hsigmaSmall
      d hd hdNear hdZero hdBounds hdDeriv a ha haCorrection haLarge
    have hth := (hscalar.2.1 1 ⟨by norm_num, by norm_num⟩).2.2 0 hb0
    have htlo : 0 < theta 0 1 := hth.1
    have hthi : theta 0 1 < Real.pi / 2 := hth.2.1
    have hr0 : 0 < r 0 := (hscalar.1 0 hb0).1
    have hA0 : 0 < A 0 := by dsimp only [A]; linarith only [hthi, Real.pi_pos]
    have hcos : 0 < Real.cos (theta 0 1) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith only [htlo, Real.pi_pos], hthi⟩
    have hpos : 0 < a * r 0 * A 0 * Real.cos (theta 0 1) := by positivity
    have hangle : Real.cos (theta 0 1 + A 0 * (k : ℝ)) = Real.cos (theta 0 1) := by
      fin_cases k
      · simp
      · norm_num only [Fin.isValue, Fin.val_one, Nat.cast_one, mul_one]
        rw [show theta 0 1 + A 0 = 2 * Real.pi - theta 0 1 by dsimp only [A]; ring,
          Real.cos_two_pi_sub]
    have hf : (fun t => (J2 (M i 0 t)).1) =ᶠ[𝓝 (k : ℝ)]
        fun t => eps i * a * r 0 * Real.sin (theta 0 1 + A 0 * t) / Real.sqrt 2 := by
      filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hUopen.mem_nhds (hkU k))] with t ht
      rw [hJM, (hQ i).2.2.2.2.1 (t, 0) ht]
      change a * (eps i * r 0 * Real.sin (phi (t, 0))) / Real.sqrt 2 = _
      dsimp only [phi]
      ring
    have hg : (fun t => (J2 (M i 0 t)).1) =ᶠ[𝓝 (k : ℝ)]
        fun t => ‖M i 0 t‖ * (eps k * eps i / Real.sqrt 2) := by
      filter_upwards [Metric.ball_mem_nhds (k : ℝ) heta] with t ht
      have he := (hEnd i k t (by simpa only [mem_ball, Real.dist_eq] using ht)).2
      calc
        (J2 (M i 0 t)).1 = (J2 (‖M i 0 t‖ • port (ep (i, k)))).1 :=
          congrArg (fun x => (J2 x).1) he
        _ = _ := by rw [map_smul, hPortJ]; rfl
    have hh := ((hasDerivAt_id (k : ℝ)).const_mul (A 0)).const_add (theta 0 1)
    simp only [mul_one, id_eq] at hh
    have hs := (hh.sin.const_mul (eps i * a * r 0)).div_const (Real.sqrt 2)
    have hn := ((hNormsm i k (hkU k)).differentiableAt (by simp)).hasDerivAt.mul_const
      (eps k * eps i / Real.sqrt 2)
    have he := (hs.congr_of_eventuallyEq hf).unique (hn.congr_of_eventuallyEq hg)
    rw [hangle] at he
    field_simp at he
    fin_cases i <;> fin_cases k <;> norm_num [eps, r] at he hpos ⊢ <;>
      nlinarith only [he, hpos]
  let f0 : Fin 2 → ℝ → ℝ := fun i t => ‖M i 0 t‖ - 1
  let f1 : Fin 2 → ℝ → ℝ := fun i t => 2 - ‖M i 0 t‖
  have hf0 (i : Fin 2) : ContDiffOn ℝ ∞ (f0 i) (Ioo (-eta) eta) := by
    intro t ht
    exact ((hNormsm i t (hEnd i 0 t (by simpa using abs_lt.mpr ht)).1).sub
      contDiffAt_const).contDiffWithinAt
  have hf1 (i : Fin 2) : ContDiffOn ℝ ∞ (f1 i) (Ioo (1 - eta) (1 + eta)) := by
    intro t ht
    have hh : |t - (1 : Fin 2)| < eta := abs_lt.mpr
      ⟨by norm_num; linarith only [ht.1], by norm_num; linarith only [ht.2]⟩
    exact (contDiffAt_const.sub (hNormsm i t (hEnd i 1 t hh).1)).contDiffWithinAt
  obtain ⟨nu, Theta, hnu, hnuSmall, hTheta⟩ := exists_saddle_endpoint_reparametrizations
    2 eta heta (by linarith only [heta0, heta0Small]) f0 f1 hf0 hf1
    (fun i => by
      have he : M i 0 0 = port (ep (i, 0)) := by simpa using hport i 0
      simp only [f0, he, hportNorm, sub_self])
    (fun i => by
      have he : M i 0 1 = port (ep (i, 1)) := by simpa using hport i 1
      simp only [f1, he, hportNorm]; norm_num)
    (fun i => by
      have hs : (0, 0) ∈ U := by simpa using hkU 0
      have he := (((hNormsm i 0 hs).differentiableAt (by simp)).hasDerivAt.sub_const 1).deriv
      change deriv (f0 i) 0 = _ at he
      rw [he]
      simpa [eps] using hRadialDeriv i 0)
    (fun i => by
      have hs : (1, 0) ∈ U := by simpa using hkU 1
      have he := (((hNormsm i 1 hs).differentiableAt (by simp)).hasDerivAt.const_sub 2).deriv
      change deriv (f1 i) 1 = _ at he
      rw [he]
      simpa [eps] using hRadialDeriv i 1)
  let alpha : Fin 2 → ℝ → E2 := fun i t => M i 0 (Theta i t)
  have hTI (i : Fin 2) : Theta i '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 :=
    (hTheta i).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTM (i : Fin 2) : MapsTo (Theta i) (Icc (-nu) (1 + nu)) (Ioo (-eta) (1 + eta)) :=
    (hTheta i).2.2.2.2.2.1
  have hAlphaImage (i : Fin 2) : alpha i '' Icc (0 : ℝ) 1 = M i 0 '' Icc (0 : ℝ) 1 := by
    change (M i 0 ∘ Theta i) '' Icc (0 : ℝ) 1 = _
    rw [image_comp, hTI]
  refine ⟨eta, Q, heta, heta0.trans heta0Small, ?_, hrect, hclosed, hreg, ?_, hradM,
    nu, Theta, hnu, hnuSmall, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hs, ht, hf, hg, he, hi, hh⟩ := hQ i
    exact ⟨hs, ht, hf, hg, he, hi, hh, (hMsm i).mono hrect⟩
  · intro h hh
    refine ⟨fun i => ⟨fun t ht => (hMt i h t (hrect ⟨ht, hh⟩)).contDiffWithinAt,
      (hMinj i h).mono (fun _ ht => hrect ⟨ht, hh⟩),
      fun t ht => hMderiv i h t (hrect ⟨ht, hh⟩), ?_, ?_⟩,
      hdisjoint h hh, hcover h hh⟩
    · intro t ht
      exact hsign i h t (hrect ⟨⟨by linarith only [heta, ht.1],
        by linarith only [heta, ht.2]⟩, hh⟩)
    · intro t ht
      exact (hnormWall i h t (hrect ⟨⟨by linarith only [heta, ht.1],
        by linarith only [heta, ht.2]⟩, hh⟩)).2.mpr ht
  · intro i
    obtain ⟨hm, hmi, hdT, hT0, hT1, hMaps, hMaps0, hMaps1, heq0, heq1,
      hi0, hi1, hIc, hIo, hiC, hiO⟩ := hTheta i
    have htU (t : ℝ) (ht : t ∈ Ioo (-nu) (1 + nu)) : (Theta i t, 0) ∈ U :=
      hrect ⟨hMaps ⟨ht.1.le, ht.2.le⟩, hzero⟩
    refine ⟨hm, hmi, hdT, hT0, hT1, hIc, hMaps, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have hc := (hMt i 0 (Theta i t) (htU t ht)).comp t (Theta i).contDiff.contDiffAt
      exact hc.contDiffWithinAt
    · intro s hs t ht he
      exact (Theta i).injective (hMinj i 0 (htU s hs) (htU t ht) he)
    · intro t ht
      have hd := ((hMt i 0 (Theta i t) (htU t ht)).differentiableAt (by simp)).hasDerivAt.scomp t
        ((Theta i).contDiff.differentiable (by simp) t).hasDerivAt
      change deriv (M i 0 ∘ Theta i) t ≠ 0
      rw [hd.deriv]
      exact smul_ne_zero (hdT t).ne' (hMderiv i 0 (Theta i t) (htU t ht))
    · intro t ht
      exact hsign i 0 (Theta i t) (htU t ⟨by linarith only [ht.1, hnu],
        by linarith only [ht.2, hnu]⟩)
    · intro t ht
      have hT : Theta i t ∈ Ioo (0 : ℝ) 1 := by
        rw [← hT0, ← hT1]
        exact ⟨hm ht.1, hm ht.2⟩
      exact (hnormWall i 0 (Theta i t) (htU t ⟨by linarith only [ht.1, hnu],
        by linarith only [ht.2, hnu]⟩)).2.mpr hT
    · intro t ht
      have hc : t ∈ Icc (-nu) nu := ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩
      have hg := (hEnd i 0 (Theta i t) (by simpa using abs_lt.mpr (hMaps0 hc))).2
      have he := heq0 hc
      change ‖M i 0 (Theta i t)‖ - 1 = t at he
      change M i 0 (Theta i t) = _
      rw [hg, show ‖M i 0 (Theta i t)‖ = 1 + t by linarith only [he]]
    · intro t ht
      have hc : t ∈ Icc (1 - nu) (1 + nu) :=
        ⟨by linarith only [(abs_lt.mp ht).1], by linarith only [(abs_lt.mp ht).2]⟩
      have hg := (hEnd i 1 (Theta i t) (abs_lt.mpr
        ⟨by norm_num; linarith only [(hMaps1 hc).1],
          by norm_num; linarith only [(hMaps1 hc).2]⟩)).2
      have he := heq1 hc
      change 2 - ‖M i 0 (Theta i t)‖ = t at he
      change M i 0 (Theta i t) = _
      rw [hg, show ‖M i 0 (Theta i t)‖ = 2 - t by linarith only [he]]
  · change Disjoint (alpha 0 '' Icc (0 : ℝ) 1) (alpha 1 '' Icc (0 : ℝ) 1)
    rw [hAlphaImage, hAlphaImage]
    exact hdisjoint 0 hzero
  · change (⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1) =
      {x : E2 | 1 ≤ ‖x‖ ∧ lift 0 x ∈ B0.boundary}
    simpa only [hAlphaImage] using hcover 0 hzero
  · rintro i x ⟨t, ht, rfl⟩
    have hz : (Theta i t, 0) ∈ U := hrect ⟨hTM i ⟨ht.1.le, ht.2.le⟩, hzero⟩
    have hp0 : p0 (alpha i t) = (Q i (Theta i t, 0) : E3) := by
      have hn : N.symm (lift 0 (alpha i t)) = (Q i (Theta i t, 0) : E3) := by
        rw [← hN i (Theta i t, 0) hz, N.symm_apply_apply]
      rw [← hn, (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).2]
      dsimp only [p0, lift]
      ext j
      fin_cases j
      · dsimp; ring
      · dsimp; ring
      · change -1 + 2 * (J2 (alpha i t)).2 ^ 2 / a ^ 2 - d (2 * ‖alpha i t‖ ^ 2 / a ^ 2) = _
        rw [← hJ2]
        simp only [div_pow]
        congr 1 <;> ring
    have hx : p0 (alpha i t) ∈ sphere (0 : E3) 1 := by rw [hp0]; exact (Q i _).property
    refine ⟨hx, ?_⟩
    let p : UnitTwoSphere := ⟨p0 (alpha i t), hx⟩
    have hp : p = Q i (Theta i t, 0) := Subtype.ext hp0
    have hv : p ∈ V i := hp ▸ hQtarget i (Theta i t, 0) hz
    have hi : (Q i).symm p = (Theta i t, 0) := by
      rw [hp]
      exact (Q i).left_inv (by rwa [hQs])
    have hf : f p = 0 := by rw [hp]; exact hQheight i (Theta i t, 0) hz
    have hs : (P i p - theta 0 1) / A 0 = Theta i t := by
      have he := (hQ i).2.2.2.2.2.1 p hv
      change (Q i).symm p = ((P i p - theta (f p) 1) / A (f p), f p) at he
      rw [hf, hi] at he
      exact (congrArg Prod.fst he).symm
    change p ∈ V i ∧ (Q i).symm p = ((P i p - theta 0 1) / A 0, 0) ∧ _
    rw [hs, (Theta i).symm_apply_apply]
    exact ⟨hv, hi, ht, rfl⟩

end PoincareConjecture.M25.Topology3D
