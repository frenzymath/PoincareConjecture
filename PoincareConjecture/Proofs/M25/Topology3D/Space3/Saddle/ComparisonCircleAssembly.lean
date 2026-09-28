import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ComparisonParameters
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic

set_option autoImplicit false

open Set Function Filter Metric
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

set_option linter.unusedVariables false in

theorem exists_saddle_comparison_circle_assembly
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) :
    let l : ℝ := 3 * h
    let r : ℝ := 1 - 3 * h
    let eta : ℝ := h / 256
    let theta0 : ℝ := Real.arccos (3 / 4)
    let theta1 : ℝ := Real.arccos (1 / 2)
    let e : ℝ := theta0 - theta1 / 2
    let f : ℝ := theta0 + theta1 / 2
    let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
    let Umid : Set ℝ := Ioo (l - eta) (r + eta)
    let v : E2 := J2.symm (1, 0)
    let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
    let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
    let Copen : Set UnitCircle := {p | Real.cos f < ⟪v, (p : E2)⟫_ℝ}
    let Mopen : Set UnitCircle := {p | ⟪v, (p : E2)⟫_ℝ < Real.cos e}
    let param : ℝ → UnitCircle := fun theta =>
      circleDirection (J2.symm (Real.cos theta, Real.sin theta))
    let rightAngle : UnitCircle → ℝ := fun p => Real.arcsin (J2 (p : E2)).2
    let loopAngle : UnitCircle → ℝ := fun p => Real.pi +
      Complex.arg (-Complex.mk (J2 (p : E2)).1 (J2 (p : E2)).2)
    ∃ (a b : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞),
      StrictMono a ∧ StrictMono b ∧
      (∀ t : ℝ, 0 < deriv a t ∧ 0 < deriv b t) ∧
      ∀ (A : Fin 2 → Fin 2 → Fin 2 → ℝ → E2)
        (gamma : Fin 2 → ℝ → E2)
        (hA : ∀ j i k, ContDiffOn ℝ ∞ (A j i k) U ∧
          Set.InjOn (A j i k) U ∧ ∀ t ∈ U, deriv (A j i k) t ≠ 0)
        (hgamma : ∀ i, ContDiffOn ℝ ∞ (gamma i) U ∧
          Set.InjOn (gamma i) U ∧ ∀ t ∈ U, deriv (gamma i) t ≠ 0)
        (hGermRight : ∀ j i k s, |s| < h / 16 →
          gamma i s = A j i k (r + s))
        (hGermLeft : ∀ j i k s, |s - 1| < h / 16 →
          gamma i s = A j i k (l + s - 1))
        (hmeet : ∀ j i k,
          (gamma i '' Icc (0 : ℝ) 1) ∩ (A j i k '' Icc l r) =
            {A j i k l, A j i k r}),
        ∃ (Q : OpenPartialHomeomorph ℝ UnitCircle)
          (c : Fin 2 → Fin 2 → Fin 2 → UnitCircle → E2)
          (Z : OpenPartialHomeomorph UnitCircle ℝ),
        let q : ℝ → UnitCircle := Q
        ‖v‖ = 1 ∧
        Q.source = Umid ∧ Q.target = Mopen ∧
        (∀ t : ℝ, q t = param (a t)) ∧
        (∀ p : UnitCircle, Q.symm p = a.symm (loopAngle p)) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ q Umid ∧
        ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ Q.symm Q.target ∧
        Set.InjOn q Umid ∧
        (∀ t ∈ Umid, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) q t)) ∧
        q '' Icc l r = {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ ≤ (3 / 4 : ℝ)} ∧
        ({q l, q r} : Set UnitCircle) =
          {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ = (3 / 4 : ℝ)} ∧
        (∀ j i k p, c j i k p =
          if (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ
          then gamma i (b (rightAngle p)) else A j i k (a.symm (loopAngle p))) ∧
        (∀ j i k, IsPlanarEmbedding (c j i k)) ∧
        (∀ j i k, Set.EqOn (c j i k) (c 0 i 0) Jc) ∧
        (∀ j i k t, t ∈ Umid → c j i k (q t) = A j i k t) ∧
        (∀ j i k,
          c j i k '' Dc = gamma i '' Icc (0 : ℝ) 1 ∧
          range (c j i k) = (gamma i '' Icc (0 : ℝ) 1) ∪ (A j i k '' Icc l r) ∧
          (c j i k '' Dc) ∩ (A j i k '' Icc l r) =
            {A j i k l, A j i k r}) ∧
        Z.source = Copen ∧ Z.target = Ioo (-eta) (1 + eta) ∧
        (∀ p : UnitCircle, Z p = b (rightAngle p)) ∧
        (∀ s : ℝ, Z.symm s = param (b.symm s)) ∧
        ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ Z Z.source ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ Z.symm Z.target ∧
        Jc ⊆ Z.source ∧ Z '' Dc = Icc (0 : ℝ) 1 ∧
        ∀ j i k p, p ∈ Z.source → c j i k p = gamma i (Z p) := by
  classical
  let l : ℝ := 3 * h
  let r : ℝ := 1 - 3 * h
  let eta : ℝ := h / 256
  let theta0 : ℝ := Real.arccos (3 / 4)
  let theta1 : ℝ := Real.arccos (1 / 2)
  let e : ℝ := theta0 - theta1 / 2
  let f : ℝ := theta0 + theta1 / 2
  let speed : ℝ := (theta1 / 2) / eta
  let U : Set ℝ := Ioo (-h / 8) (1 + h / 8)
  let Umid : Set ℝ := Ioo (l - eta) (r + eta)
  let v : E2 := J2.symm (1, 0)
  let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  let Copen : Set UnitCircle := {p | Real.cos f < ⟪v, (p : E2)⟫_ℝ}
  let Mopen : Set UnitCircle := {p | ⟪v, (p : E2)⟫_ℝ < Real.cos e}
  let param : ℝ → UnitCircle := fun t => circleDirection (J2.symm (Real.cos t, Real.sin t))
  let rightAngle : UnitCircle → ℝ := fun p => Real.arcsin (J2 (p : E2)).2
  let loopAngle : UnitCircle → ℝ := fun p =>
    Real.pi + Complex.arg (-Complex.mk (J2 (p : E2)).1 (J2 (p : E2)).2)
  obtain ⟨a, b, heta, hetaH, he, he0, h01, h1f, hfpi, ham, hbm, hder,
    hal0, har0, hb0, hb1, hal, har, hbl, hbr, haOpen, haClosed, haInv, hbClosed, hbOpen, hbInv⟩ :=
      exists_saddle_comparison_parameters h hh hsmall
  change 0 < eta at heta
  change eta < h / 128 at hetaH
  change 0 < e at he
  change e < theta0 at he0
  change theta0 < theta1 at h01
  change theta1 < f at h1f
  change f < Real.pi / 2 at hfpi
  change a l = theta0 at hal0
  change a r = 2 * Real.pi - theta0 at har0
  change b (-theta0) = 0 at hb0
  change b theta0 = 1 at hb1
  change ∀ t ∈ Icc (l - eta) (l + eta), a t = theta0 + speed * (t - l) at hal
  change ∀ t ∈ Icc (r - eta) (r + eta),
    a t = 2 * Real.pi - theta0 + speed * (t - r) at har
  change ∀ theta ≤ -e, b theta = (theta + theta0) / speed at hbl
  change ∀ theta, e ≤ theta → b theta = 1 + (theta - theta0) / speed at hbr
  change a '' Umid = Ioo e (2 * Real.pi - e) at haOpen
  change a '' Icc l r = Icc theta0 (2 * Real.pi - theta0) at haClosed
  change a.symm '' Ioo e (2 * Real.pi - e) = Umid at haInv
  change b '' Icc (-theta0) theta0 = Icc (0 : ℝ) 1 at hbClosed
  change b '' Ioo (-f) f = Ioo (-eta) (1 + eta) at hbOpen
  change b.symm '' Ioo (-eta) (1 + eta) = Ioo (-f) f at hbInv
  refine ⟨a, b, ham, hbm, hder, ?_⟩
  intro A gamma hA hgamma hGermRight hGermLeft hmeet
  let x : UnitCircle → ℝ := fun p => (J2 (p : E2)).1
  let y : UnitCircle → ℝ := fun p => (J2 (p : E2)).2
  have ht0 : 0 < theta0 := he.trans he0
  have ht1 : 0 < theta1 := ht0.trans h01
  have hf : 0 < f := ht1.trans h1f
  have ht0pi : theta0 < Real.pi / 2 := (h01.trans h1f).trans hfpi
  have hepi : e < Real.pi / 2 := he0.trans ht0pi
  have hs : 0 < speed := div_pos (half_pos ht1) heta
  have hsEta : speed * eta = theta1 / 2 := div_mul_cancel₀ _ heta.ne'
  have hlr : l < r := by dsimp [l, r]; linarith
  have hTU : Umid ⊆ U := by
    intro t ht
    dsimp [Umid, U, l, r, eta] at *
    constructor <;> linarith [ht.1, ht.2]
  have hBU : Ioo (-eta) (1 + eta) ⊆ U := by
    intro t ht
    dsimp [U, eta] at *
    constructor <;> linarith [ht.1, ht.2]
  have hIUmid : Icc l r ⊆ Umid := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h01U : Icc (0 : ℝ) 1 ⊆ U := by intro t ht; dsimp [U]; constructor <;> linarith [ht.1, ht.2]
  have hxy (p : UnitCircle) : x p ^ 2 + y p ^ 2 = 1 := by
    simpa only [x, y, norm_eq_of_mem_sphere, one_pow] using hJ2 (p : E2)
  have hv : ‖v‖ = 1 := by
    have hv2 := hJ2 v
    simp only [v, J2.apply_symm_apply, one_pow, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hv2
    nlinarith [norm_nonneg v]
  have hcoord (p : UnitCircle) : ⟪v, (p : E2)⟫_ℝ = x p := by
    have hi := hJ2 (v + (p : E2))
    simp only [map_add, v, J2.apply_symm_apply, Prod.fst_add, Prod.snd_add, zero_add] at hi
    rw [norm_add_sq_real, hv, norm_eq_of_mem_sphere] at hi
    change (1 + x p) ^ 2 + y p ^ 2 = _ at hi
    nlinarith [hxy p]
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  have hcoords : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ (fun p : UnitCircle => J2 (p : E2)) :=
    J2.contDiff.contMDiff.comp contMDiff_coe_sphere
  have hx : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ x :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ)).contMDiff.comp hcoords
  have hy : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ y :=
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ)).contMDiff.comp hcoords
  have hparam (t : ℝ) : (param t : E2) = J2.symm (Real.cos t, Real.sin t) := by
    have hn : ‖J2.symm (Real.cos t, Real.sin t)‖ = 1 := by
      have hi := hJ2 (J2.symm (Real.cos t, Real.sin t))
      simp only [J2.apply_symm_apply] at hi
      nlinarith [Real.sin_sq_add_cos_sq t, norm_nonneg (J2.symm (Real.cos t, Real.sin t))]
    let p : UnitCircle := ⟨J2.symm (Real.cos t, Real.sin t), mem_sphere_zero_iff_norm.mpr hn⟩
    exact congrArg Subtype.val (circleDirection_coe_unit p)
  have hpcoord (t : ℝ) : x (param t) = Real.cos t ∧ y (param t) = Real.sin t := by
    simp [x, y, hparam]
  have hparamSmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ param := by
    apply contMDiffOn_univ.mp
    apply contMDiffOn_sphere_of_coe isOpen_univ param
    have hc : (fun t => (param t : E2)) = fun t => J2.symm (Real.cos t, Real.sin t) := funext hparam
    rw [hc]
    exact (J2.symm.contDiff.comp (Real.contDiff_cos.prodMk Real.contDiff_sin)).contMDiff.contMDiffOn
  have hpPeriod (t : ℝ) : param (2 * Real.pi + t) = param t := by
    apply Subtype.ext
    rw [hparam, hparam]
    congr 1
    ext <;> simp [Real.cos_add, Real.sin_add]
  have hRightParam (t : ℝ) (ht : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
      rightAngle (param t) = t := by
    change Real.arcsin (y (param t)) = t
    rw [(hpcoord t).2, Real.arcsin_sin ht.1 ht.2]
  have hRight (p : UnitCircle) (hp : 0 < x p) :
      rightAngle p ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧ param (rightAngle p) = p := by
    have hyb : -1 < y p ∧ y p < 1 := by
      constructor <;> nlinarith [hxy p, sq_pos_of_pos hp]
    have ha : rightAngle p ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arcsin.mpr hyb.1, Real.arcsin_lt_pi_div_two.mpr hyb.2⟩
    have hsin : Real.sin (rightAngle p) = y p := Real.sin_arcsin hyb.1.le hyb.2.le
    have hcos : Real.cos (rightAngle p) = x p := by
      apply (sq_eq_sq₀ (Real.cos_pos_of_mem_Ioo ha).le hp.le).mp
      have hc := Real.sin_sq_add_cos_sq (rightAngle p)
      rw [hsin] at hc
      nlinarith [hxy p]
    refine ⟨ha, ?_⟩
    apply Subtype.ext
    apply J2.injective
    rw [hparam, J2.apply_symm_apply]
    exact Prod.ext hcos hsin
  have hRightSmooth (p : UnitCircle) (hp : 0 < x p) : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ rightAngle p := by
    have hyb : -1 < y p ∧ y p < 1 := by
      constructor <;> nlinarith [hxy p, sq_pos_of_pos hp]
    exact (Real.contDiffAt_arcsin (ne_of_gt hyb.1) (ne_of_lt hyb.2)).comp_contMDiffAt (hy p)
  let z : UnitCircle → ℂ := fun p => Complex.mk (x p) (y p)
  have hzSmooth : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ z :=
    Complex.equivRealProdCLM.symm.contDiff.contMDiff.comp hcoords
  have hznorm (p : UnitCircle) : ‖z p‖ = 1 := by
    have hn : ‖z p‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa [z, Complex.normSq_apply, pow_two] using hxy p
    nlinarith [norm_nonneg (z p)]
  have hzSlit (p : UnitCircle) (hp : x p < 1) : -z p ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hzero : y p = 0
    · left; change 0 < -x p; nlinarith [hxy p]
    · right; simpa only [z, Complex.neg_im, ne_eq, neg_eq_zero] using hzero
  have hLoop (p : UnitCircle) (hp : x p < 1) :
      loopAngle p ∈ Ioo (0 : ℝ) (2 * Real.pi) ∧ param (loopAngle p) = p := by
    have ha : Complex.arg (-z p) < Real.pi :=
      lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.slitPlane_arg_ne_pi (hzSlit p hp))
    have hn : ‖-z p‖ = 1 := by rw [norm_neg, hznorm]
    have hne : -z p ≠ 0 := by intro hz; simp [hz] at hn
    have hc := Complex.cos_arg hne
    have hs' := Complex.sin_arg (-z p)
    rw [hn, div_one] at hc hs'
    refine ⟨⟨by change 0 < Real.pi + Complex.arg (-z p); linarith [Complex.neg_pi_lt_arg (-z p)],
      by change Real.pi + Complex.arg (-z p) < 2 * Real.pi; linarith⟩, ?_⟩
    apply Subtype.ext
    apply J2.injective
    rw [hparam, J2.apply_symm_apply]
    apply Prod.ext
    · change Real.cos (Real.pi + Complex.arg (-z p)) = x p
      simpa [Real.cos_add, z] using congrArg Neg.neg hc
    · change Real.sin (Real.pi + Complex.arg (-z p)) = y p
      simpa [Real.sin_add, z] using congrArg Neg.neg hs'
  have hLoopParam (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (2 * Real.pi)) : loopAngle (param t) = t := by
    have hz : -z (param t) = (Real.cos (t - Real.pi) : ℂ) + Real.sin (t - Real.pi) * Complex.I := by
      apply Complex.ext <;>
        simp [z, (hpcoord t).1, (hpcoord t).2, Real.cos_sub_pi, Real.sin_sub_pi,
          -Complex.ofReal_cos, -Complex.ofReal_sin]
    have harg : Complex.arg ((Real.cos (t - Real.pi) : ℂ) +
        Real.sin (t - Real.pi) * Complex.I) = t - Real.pi := by
      simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
        (Complex.arg_cos_add_sin_mul_I (θ := t - Real.pi)
          ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    change Real.pi + Complex.arg (-z (param t)) = t
    rw [hz, harg]
    ring
  have hLoopSmooth (p : UnitCircle) (hp : x p < 1) : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ loopAngle p := by
    have hl : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun q => Complex.log (-z q)) p :=
      ((Complex.contDiffAt_log (hzSlit p hp)).restrict_scalars ℝ).comp_contMDiffAt
        (f := fun q : UnitCircle => -z q) (hzSmooth.neg p)
    have him := Complex.imCLM.contDiff.comp_contMDiffAt hl
    change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun q : UnitCircle => (Complex.log (-z q)).im) p at him
    have hsum := (contMDiffAt_const (c := Real.pi)).add him
    change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun q : UnitCircle => Real.pi + (Complex.log (-z q)).im) p at hsum
    simpa only [Complex.log_im, loopAngle, z, x, y] using hsum
  have hcos0 : Real.cos theta0 = (3 / 4 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hcos1 : Real.cos theta1 = (1 / 2 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hcosf : 0 < Real.cos f ∧ Real.cos f < (1 / 2 : ℝ) := by
    refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, hfpi⟩, ?_⟩
    rw [← hcos1]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi ht1.le (by linarith [Real.pi_pos]) h1f
  have hcose : (1 / 2 : ℝ) < Real.cos e ∧ Real.cos e < 1 := by
    constructor
    · rw [← hcos1]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi he.le
        (by linarith [Real.pi_pos]) (he0.trans h01)
    · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi
        (by norm_num : (0 : ℝ) ≤ 0) (by linarith [Real.pi_pos]) he
  have hAbsCos (t g : ℝ) (ht : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hg : g ∈ Icc 0 Real.pi) :
      (Real.cos g < Real.cos t ↔ |t| < g) ∧ (Real.cos g ≤ Real.cos t ↔ |t| ≤ g) := by
    have hat : |t| ∈ Icc (0 : ℝ) Real.pi := ⟨abs_nonneg _, by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]⟩
    rw [← Real.cos_abs t]
    exact ⟨Real.strictAntiOn_cos.lt_iff_gt hg hat, Real.strictAntiOn_cos.le_iff_ge hg hat⟩
  have hLoopOrder (g t : ℝ) (hg : g ∈ Ioo (0 : ℝ) Real.pi) (ht : t ∈ Ioo (0 : ℝ) (2 * Real.pi)) :
      (Real.cos t < Real.cos g ↔ g < t ∧ t < 2 * Real.pi - g) ∧
      (Real.cos t ≤ Real.cos g ↔ g ≤ t ∧ t ≤ 2 * Real.pi - g) := by
    by_cases htp : t ≤ Real.pi
    · have ht' : t ∈ Icc (0 : ℝ) Real.pi := ⟨ht.1.le, htp⟩
      rw [Real.strictAntiOn_cos.lt_iff_gt ht' ⟨hg.1.le, hg.2.le⟩,
        Real.strictAntiOn_cos.le_iff_ge ht' ⟨hg.1.le, hg.2.le⟩]
      constructor <;> constructor <;> intro hi
      · exact ⟨hi, by linarith [hg.2]⟩
      · exact hi.1
      · exact ⟨hi, by linarith [hg.2]⟩
      · exact hi.1
    · have ht' : 2 * Real.pi - t ∈ Icc (0 : ℝ) Real.pi := ⟨by linarith [ht.2], by linarith⟩
      have hc : Real.cos t = Real.cos (2 * Real.pi - t) := (Real.cos_two_pi_sub t).symm
      rw [hc, Real.strictAntiOn_cos.lt_iff_gt ht' ⟨hg.1.le, hg.2.le⟩,
        Real.strictAntiOn_cos.le_iff_ge ht' ⟨hg.1.le, hg.2.le⟩]
      constructor <;> constructor <;> intro hi
      · exact ⟨by linarith [hg.2], by linarith⟩
      · linarith [hi.2]
      · exact ⟨by linarith [hg.2], by linarith⟩
      · linarith [hi.2]
  have hCopen : IsOpen Copen := by
    simpa only [Copen, hcoord] using isOpen_lt continuous_const hx.continuous
  have hMopen : IsOpen Mopen := by
    simpa only [Mopen, hcoord] using isOpen_lt hx.continuous continuous_const
  have hCpos (p : UnitCircle) (hp : p ∈ Copen) : 0 < x p := by
    have hp' : Real.cos f < x p := by simpa only [Copen, mem_ofPred_eq, hcoord] using hp
    exact hcosf.1.trans hp'
  have hMlt (p : UnitCircle) (hp : p ∈ Mopen) : x p < 1 := by
    have hp' : x p < Real.cos e := by simpa only [Mopen, mem_ofPred_eq, hcoord] using hp
    exact hp'.trans hcose.2
  have hCangle (p : UnitCircle) (hp : p ∈ Copen) : rightAngle p ∈ Ioo (-f) f := by
    have hr := hRight p (hCpos p hp)
    have hc : Real.cos f < Real.cos (rightAngle p) := by
      rw [← (hpcoord (rightAngle p)).1, hr.2]
      simpa only [Copen, mem_ofPred_eq, hcoord] using hp
    exact abs_lt.mp ((hAbsCos _ _ ⟨hr.1.1.le, hr.1.2.le⟩
      ⟨hf.le, by linarith [Real.pi_pos]⟩).1.mp hc)
  have hCparam (t : ℝ) (ht : t ∈ Ioo (-f) f) : param t ∈ Copen := by
    have ht' : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc := (hAbsCos t f ht' ⟨hf.le, by linarith [Real.pi_pos]⟩).1.mpr (abs_lt.mpr ht)
    simpa only [Copen, mem_ofPred_eq, hcoord, (hpcoord t).1] using hc
  have hMangle (p : UnitCircle) (hp : p ∈ Mopen) : loopAngle p ∈ Ioo e (2 * Real.pi - e) := by
    have hr := hLoop p (hMlt p hp)
    have hc : Real.cos (loopAngle p) < Real.cos e := by
      rw [← (hpcoord _).1, hr.2]
      simpa only [Mopen, mem_ofPred_eq, hcoord] using hp
    exact (hLoopOrder e _ ⟨he, by linarith [Real.pi_pos]⟩ hr.1).1.mp hc
  have hMparam (t : ℝ) (ht : t ∈ Ioo e (2 * Real.pi - e)) : param t ∈ Mopen := by
    have hc := (hLoopOrder e t ⟨he, by linarith [Real.pi_pos]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.mpr ht
    simpa only [Mopen, mem_ofPred_eq, hcoord, (hpcoord t).1] using hc
  have hqAngle (t : ℝ) (ht : t ∈ Umid) : a t ∈ Ioo e (2 * Real.pi - e) := by
    rw [← haOpen]
    exact ⟨t, ht, rfl⟩
  have hqInverse (p : UnitCircle) (hp : p ∈ Mopen) : a.symm (loopAngle p) ∈ Umid := by
    rw [← haInv]
    exact ⟨loopAngle p, hMangle p hp, rfl⟩
  have hzAngle (s : ℝ) (hs' : s ∈ Ioo (-eta) (1 + eta)) : b.symm s ∈ Ioo (-f) f := by
    rw [← hbInv]
    exact ⟨s, hs', rfl⟩
  have hzTarget (p : UnitCircle) (hp : p ∈ Copen) :
      b (rightAngle p) ∈ Ioo (-eta) (1 + eta) := by
    rw [← hbOpen]
    exact ⟨rightAngle p, hCangle p hp, rfl⟩
  have hqSmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun t => param (a t)) := hparamSmooth.comp a.contMDiff
  have hqiSmooth : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun p => a.symm (loopAngle p)) Mopen := by
    intro p hp
    exact (a.symm.contMDiff.contMDiffAt.comp p
      (hLoopSmooth p (hMlt p hp))).contMDiffWithinAt
  have hzSmooth' : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun p => b (rightAngle p)) Copen := by
    intro p hp
    exact (b.contMDiff.contMDiffAt.comp p
      (hRightSmooth p (hCpos p hp))).contMDiffWithinAt
  have hziSmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun s => param (b.symm s)) :=
    hparamSmooth.comp b.symm.contMDiff
  let Q : OpenPartialHomeomorph ℝ UnitCircle := {
    toFun := fun t => param (a t), invFun := fun p => a.symm (loopAngle p)
    source := Umid, target := Mopen
    map_source' := fun t ht => hMparam _ (hqAngle t ht)
    map_target' := hqInverse
    left_inv' := fun t ht => by
      rw [hLoopParam _ ⟨by linarith [(hqAngle t ht).1],
        by linarith [(hqAngle t ht).2]⟩, a.symm_apply_apply]
    right_inv' := fun p hp => by
      rw [a.apply_symm_apply]
      exact (hLoop p (hMlt p hp)).2
    open_source := isOpen_Ioo, open_target := hMopen
    continuousOn_toFun := hqSmooth.continuous.continuousOn
    continuousOn_invFun := hqiSmooth.continuousOn }
  let Z : OpenPartialHomeomorph UnitCircle ℝ := {
    toFun := fun p => b (rightAngle p), invFun := fun s => param (b.symm s)
    source := Copen, target := Ioo (-eta) (1 + eta)
    map_source' := hzTarget, map_target' := fun s hs' => hCparam _ (hzAngle s hs')
    left_inv' := fun p hp => by
      rw [b.symm_apply_apply]
      exact (hRight p (hCpos p hp)).2
    right_inv' := fun s hs' => by
      rw [hRightParam _ ⟨by linarith [(hzAngle s hs').1],
        by linarith [(hzAngle s hs').2]⟩, b.apply_symm_apply]
    open_source := hCopen, open_target := isOpen_Ioo
    continuousOn_toFun := hzSmooth'.continuousOn
    continuousOn_invFun := hziSmooth.continuous.continuousOn }
  have hQD : Q.MDifferentiable 𝓘(ℝ, ℝ) (𝓡 1) :=
    ⟨hqSmooth.contMDiffOn.mdifferentiableOn (by simp),
      hqiSmooth.mdifferentiableOn (by simp)⟩
  have hZD : Z.MDifferentiable (𝓡 1) 𝓘(ℝ, ℝ) :=
    ⟨hzSmooth'.mdifferentiableOn (by simp),
      hziSmooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hDcC : Dc ⊆ Copen := by
    intro p hp
    have hp' : (3 / 4 : ℝ) ≤ x p := by simpa only [Dc, mem_ofPred_eq, hcoord] using hp
    change Real.cos f < ⟪v, (p : E2)⟫_ℝ; rw [hcoord]; linarith [hcosf.2]
  have hDcAngle (p : UnitCircle) (hp : p ∈ Copen) :
      p ∈ Dc ↔ rightAngle p ∈ Icc (-theta0) theta0 := by
    have hr := hRight p (hCpos p hp)
    have hc : Real.cos (rightAngle p) = x p := by rw [← (hpcoord _).1, hr.2]
    change (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ ↔ _
    rw [hcoord, ← hc, ← hcos0,
      (hAbsCos _ _ ⟨hr.1.1.le, hr.1.2.le⟩ ⟨ht0.le, by linarith [Real.pi_pos]⟩).2]
    exact abs_le
  have hZDc : Z '' Dc = Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro s ⟨p, hp, rfl⟩
      rw [← hbClosed]
      exact ⟨rightAngle p, (hDcAngle p (hDcC hp)).mp hp, rfl⟩
    · intro s hs'
      rw [← hbClosed] at hs'
      obtain ⟨t, ht, rfl⟩ := hs'
      have htF : t ∈ Ioo (-f) f := ⟨by dsimp [f]; linarith [ht.1], by dsimp [f]; linarith [ht.2]⟩
      have hrt := hRightParam t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine ⟨param t, (hDcAngle _ (hCparam t htF)).mpr (hrt.symm ▸ ht), ?_⟩
      change b (rightAngle (param t)) = b t; rw [hrt]
  have hQClosed : Q '' Icc l r = {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ ≤ (3 / 4 : ℝ)} := by
    apply Subset.antisymm
    · rintro p ⟨t, ht, rfl⟩
      have hat : a t ∈ Icc theta0 (2 * Real.pi - theta0) := by rw [← haClosed]; exact ⟨t, ht, rfl⟩
      have hc := (hLoopOrder theta0 (a t) ⟨ht0, by linarith [Real.pi_pos]⟩
        ⟨by linarith [hat.1], by linarith [hat.2]⟩).2.mpr hat
      change ⟪v, (param (a t) : E2)⟫_ℝ ≤ (3 / 4 : ℝ)
      rw [hcoord, (hpcoord _).1, ← hcos0]; exact hc
    · intro p hp
      have hp' : x p ≤ (3 / 4 : ℝ) := by simpa only [mem_ofPred_eq, hcoord] using hp
      have hr := hLoop p (by linarith : x p < 1)
      have hc : Real.cos (loopAngle p) ≤ Real.cos theta0 := by
        rw [← (hpcoord _).1, hr.2, hcos0]
        exact hp'
      have hat := (hLoopOrder theta0 _ ⟨ht0, by linarith [Real.pi_pos]⟩ hr.1).2.mp hc
      change loopAngle p ∈ Icc theta0 (2 * Real.pi - theta0) at hat
      rw [← haClosed] at hat
      obtain ⟨t, ht, htval⟩ := hat
      exact ⟨t, ht, by change param (a t) = p; rw [htval]; exact hr.2⟩
  have hQl : ⟪v, (Q l : E2)⟫_ℝ = (3 / 4 : ℝ) := by
    change ⟪v, (param (a l) : E2)⟫_ℝ = _
    rw [hal0, hcoord, (hpcoord _).1, hcos0]
  have hQr : ⟪v, (Q r : E2)⟫_ℝ = (3 / 4 : ℝ) := by
    change ⟪v, (param (a r) : E2)⟫_ℝ = _
    rw [har0, hcoord, (hpcoord _).1, Real.cos_two_pi_sub, hcos0]
  have hQBoundary : ({Q l, Q r} : Set UnitCircle) =
      {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ = (3 / 4 : ℝ)} := by
    apply Subset.antisymm
    · intro p hp
      rcases mem_insert_iff.mp hp with hp | hp
      · subst p; exact hQl
      · rw [mem_singleton_iff] at hp; subst p; exact hQr
    · intro p hp
      have him : p ∈ Q '' Icc l r := by rw [hQClosed]; exact hp.le
      obtain ⟨t, ht, rfl⟩ := him
      by_cases htl : t = l
      · simp [htl]
      by_cases htr : t = r
      · simp [htr]
      have hat : theta0 < a t ∧ a t < 2 * Real.pi - theta0 :=
        ⟨by rw [← hal0]; exact ham (lt_of_le_of_ne ht.1 (Ne.symm htl)),
          by rw [← har0]; exact ham (lt_of_le_of_ne ht.2 htr)⟩
      have hc := (hLoopOrder theta0 (a t) ⟨ht0, by linarith [Real.pi_pos]⟩
        ⟨by linarith [hat.1], by linarith [hat.2]⟩).1.mpr hat
      have hp' : Real.cos (a t) = (3 / 4 : ℝ) := by
        change ⟪v, (param (a t) : E2)⟫_ℝ = (3 / 4 : ℝ) at hp
        rwa [hcoord, (hpcoord _).1] at hp
      rw [hp', hcos0] at hc; exact (lt_irrefl _ hc).elim

  have hOverlap (j i k : Fin 2) (p : UnitCircle) (hpC : p ∈ Copen) (hpM : p ∈ Mopen) :
      gamma i (b (rightAngle p)) = A j i k (a.symm (loopAngle p)) := by
    let t : ℝ := rightAngle p
    have htF : t ∈ Ioo (-f) f := hCangle p hpC
    have hr := hRight p (hCpos p hpC)
    have htAbs : e < |t| := by
      have hc : Real.cos t < Real.cos e := by
        rw [← (hpcoord t).1, hr.2]
        simpa only [Mopen, mem_ofPred_eq, hcoord] using hpM
      have hle := (hAbsCos t e ⟨hr.1.1.le, hr.1.2.le⟩ ⟨he.le, by linarith [Real.pi_pos]⟩).2
      exact lt_of_not_ge (fun hle' => (not_lt_of_ge (hle.mpr hle')) hc)
    by_cases htpos : 0 ≤ t
    · have hte : e < t := by simpa only [abs_of_nonneg htpos] using htAbs
      have hloop : loopAngle p = t := by
        rw [← hr.2]
        exact hLoopParam t ⟨he.trans hte, by linarith [htF.2, Real.pi_pos]⟩
      let s : ℝ := (t - theta0) / speed
      have hsEta' : |s| < eta := by
        rw [abs_lt]; constructor
        · apply (lt_div_iff₀ hs).mpr; dsimp [e] at hte; nlinarith [hsEta]
        · apply (div_lt_iff₀ hs).mpr; dsimp [f] at htF; nlinarith [htF.2, hsEta]
      have hals : a (l + s) = t := by
        rw [hal _ ⟨by linarith [(abs_lt.mp hsEta').1], by linarith [(abs_lt.mp hsEta').2]⟩]
        dsimp [s]; field_simp [hs.ne']; ring
      have hinv : a.symm (loopAngle p) = l + s := by rw [hloop, ← hals, a.symm_apply_apply]
      have hbval : b (rightAngle p) = 1 + s := hbr t hte.le
      rw [hinv, hbval, hGermLeft j i k (1 + s) (by
        simpa only [add_sub_cancel_left] using
          hsEta'.trans (by dsimp [eta]; linarith : eta < h / 16))]
      congr 1; ring
    · have htneg : t < 0 := lt_of_not_ge htpos
      have hte : t < -e := by rw [abs_of_neg htneg] at htAbs; linarith
      have hloop : loopAngle p = 2 * Real.pi + t := by
        rw [← hr.2, ← hpPeriod t]
        exact hLoopParam _ ⟨by linarith [htF.1, Real.pi_pos], by linarith⟩
      let s : ℝ := (t + theta0) / speed
      have hsEta' : |s| < eta := by
        rw [abs_lt]; constructor
        · apply (lt_div_iff₀ hs).mpr; dsimp [f] at htF; nlinarith [htF.1, hsEta]
        · apply (div_lt_iff₀ hs).mpr; dsimp [e] at hte; nlinarith [hsEta]
      have hars : a (r + s) = 2 * Real.pi + t := by
        rw [har _ ⟨by linarith [(abs_lt.mp hsEta').1], by linarith [(abs_lt.mp hsEta').2]⟩]
        dsimp [s]; field_simp [hs.ne']; ring
      have hinv : a.symm (loopAngle p) = r + s := by rw [hloop, ← hars, a.symm_apply_apply]
      have hbval : b (rightAngle p) = s := hbl t hte.le
      rw [hinv, hbval]
      exact hGermRight j i k s (hsEta'.trans (by dsimp [eta]; linarith : eta < h / 16))
  let c : Fin 2 → Fin 2 → Fin 2 → UnitCircle → E2 := fun j i k p =>
    if (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ then gamma i (Z p) else A j i k (Q.symm p)
  have hCover (p : UnitCircle) : p ∈ Copen ∨ p ∈ Mopen := by
    by_cases hp : Real.cos f < x p
    · left
      simpa only [Copen, mem_ofPred_eq, hcoord] using hp
    · right
      have hp' : x p < Real.cos e := by linarith [hcosf.2, hcose.1]
      simpa only [Mopen, mem_ofPred_eq, hcoord] using hp'
  have hcC (j i k : Fin 2) (p : UnitCircle) (hp : p ∈ Copen) : c j i k p = gamma i (Z p) := by
    dsimp only [c]
    split_ifs with hj
    · rfl
    · have hpM : p ∈ Mopen := by change ⟪v, (p : E2)⟫_ℝ < Real.cos e; linarith [hcose.1]
      exact (hOverlap j i k p hp hpM).symm
  have hcM (j i k : Fin 2) (p : UnitCircle) (hp : p ∈ Mopen) : c j i k p = A j i k (Q.symm p) := by
    dsimp only [c]
    split_ifs with hj
    · have hpC : p ∈ Copen := by change Real.cos f < ⟪v, (p : E2)⟫_ℝ; linarith [hcosf.2]
      exact hOverlap j i k p hpC hp
    · rfl
  have hcQ (j i k : Fin 2) (t : ℝ) (ht : t ∈ Umid) : c j i k (Q t) = A j i k t := by
    rw [hcM j i k _ (Q.map_source ht), Q.left_inv ht]
  have hcCap (j i k : Fin 2) : c j i k '' Dc = gamma i '' Icc (0 : ℝ) 1 := by
    rw [← hZDc, ← image_comp]
    exact image_congr (fun p hp => hcC j i k p (hDcC hp))
  have hcCapInj (j i k : Fin 2) : InjOn (c j i k) Dc := by
    intro p hp q hq hpq
    rw [hcC j i k p (hDcC hp), hcC j i k q (hDcC hq)] at hpq
    have hZp : Z p ∈ Icc (0 : ℝ) 1 := hZDc ▸ ⟨p, hp, rfl⟩
    have hZq : Z q ∈ Icc (0 : ℝ) 1 := hZDc ▸ ⟨q, hq, rfl⟩
    exact Z.injOn (hDcC hp) (hDcC hq) ((hgamma i).2.1 (h01U hZp) (h01U hZq) hpq)
  have hcCross (j i k : Fin 2) (p : UnitCircle) (hp : p ∈ Dc) (t : ℝ) (ht : t ∈ Icc l r)
      (hpt : c j i k p = A j i k t) : p = Q t := by
    have him : A j i k t ∈ (gamma i '' Icc (0 : ℝ) 1) ∩ (A j i k '' Icc l r) :=
      ⟨hcCap j i k ▸ ⟨p, hp, hpt⟩, ⟨t, ht, rfl⟩⟩
    rw [hmeet j i k, mem_insert_iff, mem_singleton_iff] at him
    rcases him with him | him
    · have ht' : t = l := (hA j i k).2.1 (hTU (hIUmid ht)) (hTU (hIUmid ⟨le_rfl, hlr.le⟩)) him
      subst t
      exact hcCapInj j i k hp (show Q l ∈ Dc from hQl.ge)
        (hpt.trans (hcQ j i k l (hIUmid ⟨le_rfl, hlr.le⟩)).symm)
    · have ht' : t = r := (hA j i k).2.1 (hTU (hIUmid ht)) (hTU (hIUmid ⟨hlr.le, le_rfl⟩)) him
      subst t
      exact hcCapInj j i k hp (show Q r ∈ Dc from hQr.ge)
        (hpt.trans (hcQ j i k r (hIUmid ⟨hlr.le, le_rfl⟩)).symm)
  have hFullCover (p : UnitCircle) : p ∈ Dc ∨ p ∈ Q '' Icc l r := by
    by_cases hp : (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ
    · exact Or.inl hp
    · right; rw [hQClosed]; exact (lt_of_not_ge hp).le
  have hcInj (j i k : Fin 2) : Injective (c j i k) := by
    intro p q hpq
    rcases hFullCover p with hp | ⟨s, hs', rfl⟩
    · rcases hFullCover q with hq | ⟨t, ht, rfl⟩
      · exact hcCapInj j i k hp hq hpq
      · exact hcCross j i k p hp t ht (hpq.trans (hcQ j i k t (hIUmid ht)))
    · rcases hFullCover q with hq | ⟨t, ht, rfl⟩
      · exact (hcCross j i k q hq s hs' (hpq.symm.trans (hcQ j i k s (hIUmid hs')))).symm
      · rw [hcQ j i k s (hIUmid hs'), hcQ j i k t (hIUmid ht)] at hpq
        exact congrArg Q ((hA j i k).2.1 (hTU (hIUmid hs')) (hTU (hIUmid ht)) hpq)
  have hCurve (g : ℝ → E2) (hg : ContDiffOn ℝ ∞ g U)
      (hreg : ∀ t ∈ U, deriv g t ≠ 0) (t : ℝ) (ht : t ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) ∞ g t ∧ Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) g t) := by
    have hd := hg.contDiffAt (isOpen_Ioo.mem_nhds ht)
    have hi : Injective (fderiv ℝ g t) := by
      intro r s hrs
      simp only [fderiv_eq_smul_deriv] at hrs
      exact smul_left_injective ℝ (hreg t ht) hrs
    refine ⟨hd.contMDiffAt, ?_⟩
    rw [mfderiv_eq_fderiv]
    convert! hi using 1
  have hcSmoothReg (j i k : Fin 2) (p : UnitCircle) :
      ContMDiffAt (𝓡 1) 𝓘(ℝ, E2) ∞ (c j i k) p ∧
        Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) (c j i k) p) := by
    rcases hCover p with hp | hp
    · have hz : Z p ∈ U := hBU (Z.map_source hp)
      have hcurve := hCurve (gamma i) (hgamma i).1 (hgamma i).2.2 (Z p) hz
      have heq : c j i k =ᶠ[𝓝 p] gamma i ∘ Z := by
        filter_upwards [hCopen.mem_nhds hp] with q hq
        exact hcC j i k q hq
      refine ⟨(hcurve.1.comp p
        (hzSmooth'.contMDiffAt (hCopen.mem_nhds hp))).congr_of_eventuallyEq heq, ?_⟩
      rw [heq.mfderiv_eq, mfderiv_comp p (hcurve.1.mdifferentiableAt (by simp))
        (hZD.mdifferentiableAt hp)]
      exact hcurve.2.comp (hZD.mfderiv_injective hp)
    · have ht : Q.symm p ∈ U := hTU (Q.map_target hp)
      have hcurve := hCurve (A j i k) (hA j i k).1 (hA j i k).2.2 (Q.symm p) ht
      have heq : c j i k =ᶠ[𝓝 p] A j i k ∘ Q.symm := by
        filter_upwards [hMopen.mem_nhds hp] with q hq
        exact hcM j i k q hq
      refine ⟨(hcurve.1.comp p
        (hqiSmooth.contMDiffAt (hMopen.mem_nhds hp))).congr_of_eventuallyEq heq, ?_⟩
      rw [heq.mfderiv_eq, mfderiv_comp p (hcurve.1.mdifferentiableAt (by simp))
        (hQD.mdifferentiableAt_symm hp)]
      exact hcurve.2.comp (hQD.symm.mfderiv_injective hp)
  have hcRange (j i k : Fin 2) :
      range (c j i k) = (gamma i '' Icc (0 : ℝ) 1) ∪ (A j i k '' Icc l r) := by
    apply Subset.antisymm
    · rintro z' ⟨p, rfl⟩
      rcases hFullCover p with hp | ⟨t, ht, rfl⟩
      · left; rw [← hcCap j i k]; exact ⟨p, hp, rfl⟩
      · right; exact ⟨t, ht, (hcQ j i k t (hIUmid ht)).symm⟩
    · intro z' hz'
      rcases hz' with hz' | ⟨t, ht, rfl⟩
      · rw [← hcCap j i k] at hz'; rcases hz' with ⟨p, _, rfl⟩; exact mem_range_self p
      · exact ⟨Q t, hcQ j i k t (hIUmid ht)⟩
  have hJcC : Jc ⊆ Copen := by
    intro p hp
    change Real.cos f < ⟪v, (p : E2)⟫_ℝ
    exact hcosf.2.trans hp
  refine ⟨Q, c, Z, hv, rfl, rfl, fun _ => rfl, fun _ => rfl, hqSmooth.contMDiffOn,
    hqiSmooth, Q.injOn, fun t ht => hQD.mfderiv_injective ht, hQClosed, hQBoundary,
    fun _ _ _ _ => rfl, ?_, ?_, hcQ, ?_, rfl, rfl, fun _ => rfl, fun _ => rfl,
    hzSmooth', hziSmooth.contMDiffOn, hJcC, hZDc, hcC⟩
  · intro j i k
    exact ⟨fun p => (hcSmoothReg j i k p).1, hcInj j i k, fun p => (hcSmoothReg j i k p).2⟩
  · intro j i k p hp
    rw [hcC j i k p (hJcC hp), hcC 0 i 0 p (hJcC hp)]
  · intro j i k
    exact ⟨hcCap j i k, hcRange j i k, by rw [hcCap j i k, hmeet j i k]⟩

end PoincareConjecture.M25.Topology3D
