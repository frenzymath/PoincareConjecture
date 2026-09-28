import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PeriodicPolarFamily
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_angular_reconnection
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmuSmall : mu ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let sigma : ℝ → ℝ := Real.smoothTransition
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let X : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
      (sx i * Real.sqrt ((r ^ 2 + a) / 2),
        sy i * Real.sqrt ((r ^ 2 - a) / 2))
    let angle : ℝ → E2 → ℝ := fun t x =>
      chi ‖x‖ *
        ((Real.arccos (-(1 - sigma t) * mu / ‖x‖ ^ 2) -
          Real.arccos (-mu / ‖x‖ ^ 2)) / 2) *
        (2 * (J2 x).1 * (J2 x).2 / ‖x‖ ^ 2) /
        Real.sqrt (1 - (-mu / ‖x‖ ^ 2) ^ 2)
    let C : Set E2 := {x | (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 3 / 2}
    ∃ F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (F p.1).symm p.2) ∧
      (∀ t x, F t x = J2.symm
        (Real.cos (angle t x) * (J2 x).1 - Real.sin (angle t x) * (J2 x).2,
          Real.sin (angle t x) * (J2 x).1 + Real.cos (angle t x) * (J2 x).2)) ∧
      (∀ t x, ‖F t x‖ = ‖x‖ ∧ ‖(F t).symm x‖ = ‖x‖) ∧
      (∀ t x, t ≤ 0 → F t x = x ∧ (F t).symm x = x) ∧
      (∀ t x, 1 ≤ t → F t x = F 1 x ∧ (F t).symm x = (F 1).symm x) ∧
      IsCompact C ∧
      (∀ t,
        tsupport (fun x : E2 => F t x - x) ⊆ C ∧
        tsupport (fun x : E2 => (F t).symm x - x) ⊆ C) ∧
      (∀ t i r, r ∈ Icc (3 / 4 : ℝ) (5 / 4) →
        F t (X (-mu) r i) = X (-(1 - sigma t) * mu) r i) ∧
      (∀ t x,
        (0 < (J2 (F t x)).1 ↔ 0 < (J2 x).1) ∧
        ((J2 (F t x)).1 = 0 ↔ (J2 x).1 = 0) ∧
        (0 < (J2 (F t x)).2 ↔ 0 < (J2 x).2) ∧
        ((J2 (F t x)).2 = 0 ↔ (J2 x).2 = 0)) := by
  classical
  let sigma : ℝ → ℝ := Real.smoothTransition
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let X : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
    (sx i * Real.sqrt ((r ^ 2 + a) / 2), sy i * Real.sqrt ((r ^ 2 - a) / 2))
  let q0 : ℝ → ℝ := fun u => -mu / u
  let qt : ℝ × ℝ → ℝ := fun p => -(1 - sigma p.1) * mu / p.2
  let d : ℝ × ℝ → ℝ := fun p => (Real.arccos (qt p) - Real.arccos (q0 p.2)) / 2
  let b : ℝ → ℝ := fun u => Real.sqrt (1 - (q0 u) ^ 2)
  let a : ℝ × ℝ → ℝ := fun p => chi (Real.sqrt p.2) * d p / b p.2
  let H : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 + a p.1 * Real.sin (2 * p.2)
  let p : ℝ → E2 := fun s => J2.symm (Real.cos s, Real.sin s)
  let angle : ℝ → E2 → ℝ := fun t x =>
    chi ‖x‖ * d (t, ‖x‖ ^ 2) * (2 * (J2 x).1 * (J2 x).2 / ‖x‖ ^ 2) / b (‖x‖ ^ 2)
  let C : Set E2 := {x | (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 3 / 2}
  have hsigma (t : ℝ) : 0 ≤ sigma t ∧ sigma t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hArgs (t u : ℝ) (hu : 1 / 4 < u) :
      -1 / 32 < q0 u ∧ q0 u ≤ qt (t, u) ∧ qt (t, u) ≤ 0 := by
    have hu0 : 0 < u := by linarith
    have hm : 0 < mu / u := div_pos hmu hu0
    have hm1 : mu / u < 1 / 32 := (div_lt_iff₀ hu0).mpr (by nlinarith)
    have hq : qt (t, u) = -(1 - sigma t) * (mu / u) := by dsimp [qt]; ring
    have h0 : q0 u = -(mu / u) := by dsimp [q0]; ring
    rw [h0, hq]
    have hp := mul_nonneg (sub_nonneg.mpr (hsigma t).2) hm.le
    have hq' := mul_nonneg (hsigma t).1 hm.le
    exact ⟨by linarith, by nlinarith, by linarith⟩
  have hB (u : ℝ) (hu : 1 / 4 < u) : 31 / 32 < b u := by
    have hh := hArgs 0 u hu
    have hq : q0 u ≤ 0 := hh.2.1.trans hh.2.2
    change (31 / 32 : ℝ) < Real.sqrt (1 - (q0 u) ^ 2)
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ q0 u + 1 / 32) hq]
  have hLip (x y : ℝ) (hx : x ∈ Icc (-1 / 32 : ℝ) 0)
      (hy : y ∈ Icc (-1 / 32 : ℝ) 0) :
      |Real.arccos y - Real.arccos x| ≤ 2 * |y - x| := by
    have hd (z : ℝ) (hz : z ∈ Icc (-1 / 32 : ℝ) 0) :
        DifferentiableAt ℝ Real.arccos z :=
      (Real.hasDerivAt_arccos (by linarith [hz.1, hz.2])
        (by linarith [hz.1, hz.2])).differentiableAt
    have hb (z : ℝ) (hz : z ∈ Icc (-1 / 32 : ℝ) 0) :
        ‖deriv Real.arccos z‖ ≤ 2 := by
      have hs : (1 / 2 : ℝ) < Real.sqrt (1 - z ^ 2) :=
        Real.lt_sqrt_of_sq_lt (by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith [hz.1] : 0 ≤ z + 1 / 32) hz.2])
      rw [Real.deriv_arccos]
      simp only [Real.norm_eq_abs, abs_neg, abs_div, abs_one,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (div_le_iff₀ (by linarith)).mpr (by linarith)
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _) hx hy
  have hD (t u : ℝ) (hu : 1 / 4 < u) : |d (t, u)| < 1 / 32 := by
    obtain ⟨hq, hqt, hqt0⟩ := hArgs t u hu
    have he := hLip (q0 u) (qt (t, u)) ⟨hq.le, hqt.trans hqt0⟩
      ⟨hq.le.trans hqt, hqt0⟩
    have hgap : |qt (t, u) - q0 u| < 1 / 32 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hqt)]
      linarith
    dsimp [d]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hCutoffDomain (u : ℝ) (hu : Real.sqrt u ∈ tsupport chi) : 1 / 4 < u := by
    have hr := (hchiSupport hu).1
    have hu0 : 0 < u := Real.sqrt_pos.mp (by linarith)
    have hs := Real.sq_sqrt hu0.le
    nlinarith
  have hA (t u : ℝ) : |a (t, u)| < 1 / 31 := by
    by_cases hc : chi (Real.sqrt u) = 0
    · simp only [a, hc, zero_mul, zero_div]
      norm_num
    · have hu := hCutoffDomain u (subset_tsupport chi hc)
      have hbu := hB u hu
      have hdu := hD t u hu
      have hb0 : 0 < b u := by linarith
      dsimp [a]
      rw [abs_div, abs_mul, abs_of_nonneg (hchiBounds _).1, abs_of_pos hb0]
      apply (div_lt_iff₀ hb0).mpr
      have hm := mul_le_mul_of_nonneg_right (hchiBounds (Real.sqrt u)).2 (abs_nonneg (d (t, u)))
      nlinarith
  have hSmoothA : ContDiff ℝ ∞ a := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : Real.sqrt z.2 ∈ tsupport chi
    · have hu := hCutoffDomain z.2 hz
      have hu0 : z.2 ≠ 0 := by linarith
      obtain ⟨hq, hqt, hqt0⟩ := hArgs z.1 z.2 hu
      have hq0 : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => q0 v.2) z :=
        contDiffAt_const.div contDiffAt_snd hu0
      have hq1 : ContDiffAt ℝ ∞ qt z :=
        ((contDiffAt_const.sub
          (Real.smoothTransition.contDiff.comp contDiff_fst).contDiffAt).neg.mul
            contDiffAt_const).div contDiffAt_snd hu0
      have hd0 := (Real.contDiffAt_arccos (by linarith : q0 z.2 ≠ -1)
        (by linarith : q0 z.2 ≠ 1)).comp z hq0
      have hd1 := (Real.contDiffAt_arccos (by linarith : qt z ≠ -1)
        (by linarith : qt z ≠ 1)).comp z hq1
      have hrad : 0 < 1 - (q0 z.2) ^ 2 := by
        have hh := hB z.2 hu
        exact Real.sqrt_pos.mp (by change 0 < b z.2; linarith)
      have hb : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => b v.2) z :=
        (contDiffAt_const.sub (hq0.pow 2)).sqrt hrad.ne'
      have hc : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => chi (Real.sqrt v.2)) z :=
        hchi.contDiffAt.comp z (contDiffAt_snd.sqrt hu0)
      exact (hc.mul ((hd1.sub hd0).div_const 2)).div hb
        (by have hh := hB z.2 hu; linarith)
    · have hn : ∀ᶠ v : ℝ × ℝ in 𝓝 z, Real.sqrt v.2 ∉ tsupport chi :=
        (isClosed_tsupport chi).isOpen_compl.preimage
          (Real.continuous_sqrt.comp continuous_snd) |>.mem_nhds hz
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) z).congr_of_eventuallyEq
      filter_upwards [hn] with v hv
      simp only [a, image_eq_zero_of_notMem_tsupport hv, zero_mul, zero_div]
  have hSmoothH : ContDiff ℝ ∞ H :=
    contDiff_snd.add ((hSmoothA.comp contDiff_fst).mul
      ((contDiff_const.mul contDiff_snd).sin))
  have hPer (t u s : ℝ) : H ((t, u), s + 2 * Real.pi) = H ((t, u), s) + 2 * Real.pi := by
    dsimp [H]
    rw [show 2 * (s + 2 * Real.pi) = (2 * s + 2 * Real.pi) + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_add_two_pi]
    ring
  have hPos (t u s : ℝ) : 0 < deriv (fun v : ℝ => H ((t, u), v)) s := by
    have hd : HasDerivAt (fun v : ℝ => H ((t, u), v))
        (1 + a (t, u) * (Real.cos (2 * s) * 2)) s := by
      convert! (hasDerivAt_id s).add
        ((((hasDerivAt_id s).const_mul 2).sin).const_mul (a (t, u))) using 1
      simp only [id_eq]
      ring
    rw [hd.deriv]
    have hb : |a (t, u) * Real.cos (2 * s)| < 1 / 31 := calc
      |a (t, u) * Real.cos (2 * s)| = |a (t, u)| * |Real.cos (2 * s)| := abs_mul _ _
      _ ≤ |a (t, u)| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ < 1 / 31 := hA t u
    have hh := neg_abs_le (a (t, u) * Real.cos (2 * s))
    nlinarith
  have hInner (t u s : ℝ) (hu : u ≤ 1 / 4) : H ((t, u), s) = s := by
    have hr : Real.sqrt u ≤ 1 / 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
    have hc : chi (Real.sqrt u) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => not_lt_of_ge hr (hchiSupport h).1)
    simp only [H, a, hc, zero_mul, zero_div, add_zero]
  obtain ⟨F, hF, hFi, hNorm, hPolar, hFixFiber⟩ := exists_saddle_periodic_polar_family
    J2 hJ2 H hSmoothH hPer hPos (1 / 4) (by norm_num) hInner
  have hPcoord (r s : ℝ) : J2 (r • p s) = (r * Real.cos s, r * Real.sin s) := by
    simp only [p, map_smul, J2.apply_symm_apply, Prod.smul_mk, smul_eq_mul]
  have hRep (x : E2) : ∃ s : ℝ, x = ‖x‖ • p s := by
    let z : ℂ := Complex.equivRealProdCLM.symm (J2 x)
    have hn : ‖z‖ = ‖x‖ := by
      have hz := Complex.sq_norm z
      have hx := hJ2 x
      simp only [Complex.normSq_apply, z, Complex.equivRealProdCLM_symm_apply_re,
        Complex.equivRealProdCLM_symm_apply_im] at hz
      nlinarith [norm_nonneg z, norm_nonneg x]
    refine ⟨Complex.arg z, ?_⟩
    apply J2.injective
    rw [hPcoord, ← hn]
    apply Prod.ext
    · simpa only [z, Complex.equivRealProdCLM_symm_apply_re] using (Complex.norm_mul_cos_arg z).symm
    · simpa only [z, Complex.equivRealProdCLM_symm_apply_im] using (Complex.norm_mul_sin_arg z).symm
  have hFormula (t : ℝ) (x : E2) : F t x = J2.symm
      (Real.cos (angle t x) * (J2 x).1 - Real.sin (angle t x) * (J2 x).2,
        Real.sin (angle t x) * (J2 x).1 + Real.cos (angle t x) * (J2 x).2) := by
    by_cases hx : x = 0
    · subst x
      have hf : F t (0 : E2) = 0 := norm_eq_zero.mp (by
        simpa only [norm_zero] using (hNorm t 0).1)
      rw [hf]
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero, zero_add]
      exact (map_zero J2.symm).symm
    · obtain ⟨s, hs⟩ := hRep x
      have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hcoords : J2 x = (‖x‖ * Real.cos s, ‖x‖ * Real.sin s) :=
        (congrArg J2 hs).trans (hPcoord ‖x‖ s)
      have hang : angle t x = a (t, ‖x‖ ^ 2) * Real.sin (2 * s) := by
        dsimp only [angle, a]
        rw [Real.sqrt_sq (norm_nonneg x), hcoords]
        have hfrac : 2 * (‖x‖ * Real.cos s) * (‖x‖ * Real.sin s) / ‖x‖ ^ 2 = Real.sin (2 * s) := by
          rw [Real.sin_two_mul]
          field_simp [hr]
        rw [hfrac]
        ring
      have hf : F t x = ‖x‖ • p (H ((t, ‖x‖ ^ 2), s)) :=
        (congrArg (F t) hs).trans (hPolar t ‖x‖ (norm_nonneg x) s)
      apply J2.injective
      rw [hf, hPcoord, J2.apply_symm_apply, hcoords]
      change (‖x‖ * Real.cos (s + a (t, ‖x‖ ^ 2) * Real.sin (2 * s)),
        ‖x‖ * Real.sin (s + a (t, ‖x‖ ^ 2) * Real.sin (2 * s))) = _
      rw [← hang, Real.cos_add, Real.sin_add]
      apply Prod.ext <;> ring
  have hInitial (t : ℝ) (ht : t ≤ 0) (x : E2) : F t x = x ∧ (F t).symm x = x := by
    apply hFixFiber
    intro s
    simp [H, a, d, qt, q0, sigma, Real.smoothTransition.zero_of_nonpos ht]
  have hTerminal (t : ℝ) (ht : 1 ≤ t) (x : E2) :
      F t x = F 1 x ∧ (F t).symm x = (F 1).symm x := by
    have hf (y : E2) : F t y = F 1 y := by
      rw [hFormula, hFormula]
      congr 1
      simp only [angle, d, qt, sigma, Real.smoothTransition.one_of_one_le ht,
        Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 1 from le_rfl)]
    refine ⟨hf x, ?_⟩
    apply (F 1).injective
    change F 1 ((F t).symm x) = F 1 ((F 1).symm x)
    calc
      _ = F t ((F t).symm x) := (hf _).symm
      _ = x := (F t).apply_symm_apply x
      _ = _ := ((F 1).apply_symm_apply x).symm
  have hClosed : IsClosed C :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hCompact : IsCompact C := (isCompact_closedBall (0 : E2) (3 / 2)).of_isClosed_subset
    hClosed (fun x hx => by simpa only [mem_closedBall, dist_zero_right] using hx.2)
  have hOutside (t : ℝ) (x : E2) (hx : x ∉ C) : F t x = x ∧ (F t).symm x = x := by
    have hc : chi ‖x‖ = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx ⟨(hchiSupport h).1.le, (hchiSupport h).2.le⟩)
    apply hFixFiber
    intro s
    simp only [H, a, Real.sqrt_sq (norm_nonneg x), hc, zero_mul, zero_div, add_zero]
  have hSupport (t : ℝ) : tsupport (fun x : E2 => F t x - x) ⊆ C ∧
      tsupport (fun x : E2 => (F t).symm x - x) ⊆ C := by
    constructor
    · apply closure_minimal ?_ hClosed
      intro x hx
      by_contra hn
      exact hx (sub_eq_zero.mpr (hOutside t x hn).1)
    · apply closure_minimal ?_ hClosed
      intro x hx
      by_contra hn
      exact hx (sub_eq_zero.mpr (hOutside t x hn).2)
  let ang : ℝ → Fin 4 → ℝ := fun v => ![v, Real.pi - v, Real.pi + v, 2 * Real.pi - v]
  have hAngShift (v e : ℝ) (i : Fin 4) : ang (v + e) i = ang v i + sx i * sy i * e := by
    fin_cases i <;> simp [ang, sx, sy] <;> ring
  have hAngSin (v : ℝ) (i : Fin 4) : Real.sin (2 * ang v i) = sx i * sy i * Real.sin (2 * v) := by
    fin_cases i
    · simp [ang, sx, sy]
    · dsimp [ang, sx, sy]
      rw [show 2 * (Real.pi - v) = 2 * Real.pi - 2 * v by ring, Real.sin_sub]
      simp
    · dsimp [ang, sx, sy]
      rw [show 2 * (Real.pi + v) = 2 * v + 2 * Real.pi by ring, Real.sin_add_two_pi]
      ring
    · dsimp [ang, sx, sy]
      rw [show 2 * (2 * Real.pi - v) = (2 * Real.pi - 2 * v) + 2 * Real.pi by ring,
        Real.sin_add_two_pi, Real.sin_sub]
      simp
  have hHalf (z r : ℝ) (hr : 0 < r) (hz : -r ^ 2 ≤ z ∧ z ≤ r ^ 2) :
      r * Real.cos (Real.arccos (z / r ^ 2) / 2) = Real.sqrt ((r ^ 2 + z) / 2) ∧
      r * Real.sin (Real.arccos (z / r ^ 2) / 2) = Real.sqrt ((r ^ 2 - z) / 2) := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hq1 : -1 ≤ z / r ^ 2 := (le_div_iff₀ hr2).mpr (by nlinarith [hz.1])
    have hq2 : z / r ^ 2 ≤ 1 := (div_le_iff₀ hr2).mpr (by nlinarith [hz.2])
    have hlo := Real.arccos_nonneg (z / r ^ 2)
    have hhi := Real.arccos_le_pi (z / r ^ 2)
    have hcos := Real.cos_half (by linarith : -Real.pi ≤ Real.arccos (z / r ^ 2)) hhi
    have hsin := Real.sin_half_eq_sqrt hlo (by linarith : Real.arccos (z / r ^ 2) ≤ 2 * Real.pi)
    rw [Real.cos_arccos hq1 hq2] at hcos hsin
    constructor
    · rw [hcos]
      calc
        r * Real.sqrt ((1 + z / r ^ 2) / 2) =
            Real.sqrt (r ^ 2) * Real.sqrt ((1 + z / r ^ 2) / 2) := by rw [Real.sqrt_sq hr.le]
        _ = Real.sqrt (r ^ 2 * ((1 + z / r ^ 2) / 2)) := (Real.sqrt_mul (sq_nonneg r) _).symm
        _ = Real.sqrt ((r ^ 2 + z) / 2) := by congr 1; field_simp [hr.ne']
    · rw [hsin]
      calc
        r * Real.sqrt ((1 - z / r ^ 2) / 2) =
            Real.sqrt (r ^ 2) * Real.sqrt ((1 - z / r ^ 2) / 2) := by rw [Real.sqrt_sq hr.le]
        _ = Real.sqrt (r ^ 2 * ((1 - z / r ^ 2) / 2)) := (Real.sqrt_mul (sq_nonneg r) _).symm
        _ = Real.sqrt ((r ^ 2 - z) / 2) := by congr 1; field_simp [hr.ne']
  have hXpolar (z r : ℝ) (hr : 0 < r) (hz : -r ^ 2 ≤ z ∧ z ≤ r ^ 2) (i : Fin 4) :
      X z r i = r • p (ang (Real.arccos (z / r ^ 2) / 2) i) := by
    obtain ⟨hc, hs⟩ := hHalf z r hr hz
    have htrig (v : ℝ) (k : Fin 4) :
        Real.cos (ang v k) = sx k * Real.cos v ∧
          Real.sin (ang v k) = sy k * Real.sin v := by
      fin_cases k <;> simp [ang, sx, sy, Real.cos_sub, Real.sin_sub,
        Real.cos_add, Real.sin_add]
    apply J2.injective
    rw [hPcoord]
    change J2 (J2.symm
      (sx i * Real.sqrt ((r ^ 2 + z) / 2), sy i * Real.sqrt ((r ^ 2 - z) / 2))) = _
    rw [J2.apply_symm_apply]
    rw [(htrig _ i).1, (htrig _ i).2, ← hc, ← hs]
    apply Prod.ext <;> ring
  have hBranches (t : ℝ) (i : Fin 4) (r : ℝ) (hr : r ∈ Icc (3 / 4 : ℝ) (5 / 4)) :
      F t (X (-mu) r i) = X (-(1 - sigma t) * mu) r i := by
    have hr0 : 0 < r := by linarith [hr.1]
    have hr2 : 1 / 4 < r ^ 2 := by nlinarith [hr.1]
    have hz0 : -r ^ 2 ≤ -mu ∧ -mu ≤ r ^ 2 := by constructor <;> nlinarith [hr.1]
    have hz1 : -r ^ 2 ≤ -(1 - sigma t) * mu ∧ -(1 - sigma t) * mu ≤ r ^ 2 := by
      have h0 := mul_nonneg (hsigma t).1 hmu.le
      have h1 := mul_nonneg (sub_nonneg.mpr (hsigma t).2) hmu.le
      constructor <;> nlinarith [hr.1]
    let v0 := Real.arccos (q0 (r ^ 2)) / 2
    have hv : Real.arccos (qt (t, r ^ 2)) / 2 = v0 + d (t, r ^ 2) := by dsimp [v0, d]; ring
    have hsin : Real.sin (2 * v0) = b (r ^ 2) := by
      rw [show 2 * v0 = Real.arccos (q0 (r ^ 2)) by dsimp [v0]; ring]
      exact Real.sin_arccos _
    have hb0 : b (r ^ 2) ≠ 0 := by have hh := hB (r ^ 2) hr2; linarith
    have hc : a (t, r ^ 2) = d (t, r ^ 2) / b (r ^ 2) := by
      simp only [a, Real.sqrt_sq hr0.le, hchiOne r hr, one_mul]
    have hstep : H ((t, r ^ 2), ang v0 i) = ang (Real.arccos (qt (t, r ^ 2)) / 2) i := by
      rw [hv, hAngShift]
      dsimp only [H]
      rw [hAngSin, hsin, hc]
      field_simp [hb0]
    rw [hXpolar (-mu) r hr0 hz0 i, hPolar t r hr0.le]
    change r • p (H ((t, r ^ 2), ang v0 i)) = _
    rw [hstep]
    exact (hXpolar (-(1 - sigma t) * mu) r hr0 hz1 i).symm
  have hAxis (t : ℝ) (x : E2) (hx : (J2 x).1 = 0 ∨ (J2 x).2 = 0) : F t x = x := by
    have ha0 : angle t x = 0 := by
      rcases hx with hx | hx <;> simp only [angle, hx, mul_zero, zero_mul, zero_div]
    rw [hFormula, ha0]
    simpa only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, sub_zero, zero_add]
      using J2.symm_apply_apply x
  have hZeros (t : ℝ) (x : E2) :
      ((J2 (F t x)).1 = 0 ↔ (J2 x).1 = 0) ∧ ((J2 (F t x)).2 = 0 ↔ (J2 x).2 = 0) := by
    constructor
    · constructor
      · intro h
        have he : F t x = x := (F t).injective (hAxis t (F t x) (Or.inl h))
        simpa only [he] using h
      · intro h
        rw [hAxis t x (Or.inl h), h]
    · constructor
      · intro h
        have he : F t x = x := (F t).injective (hAxis t (F t x) (Or.inr h))
        simpa only [he] using h
      · intro h
        rw [hAxis t x (Or.inr h), h]
  have hContinuousSign (f : ℝ → ℝ) (hf : Continuous f)
      (hn : ∀ t, f t = 0 ↔ f 0 = 0) (t : ℝ) : 0 < f t ↔ 0 < f 0 := by
    constructor
    · intro ht
      by_contra h0
      have hn0 : f 0 < 0 := lt_of_le_of_ne (le_of_not_gt h0)
        (fun he => ht.ne' ((hn t).mpr he))
      obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hf ⟨hn0.le, ht.le⟩
      exact hn0.ne ((hn s).mp hs)
    · intro h0
      by_contra ht
      have hnt : f t < 0 := lt_of_le_of_ne (le_of_not_gt ht)
        (fun he => h0.ne' ((hn t).mp he))
      obtain ⟨s, hs⟩ := intermediate_value_univ t 0 hf ⟨hnt.le, h0.le⟩
      exact h0.ne' ((hn s).mp hs)
  have hSigns (t : ℝ) (x : E2) :
      (0 < (J2 (F t x)).1 ↔ 0 < (J2 x).1) ∧
      ((J2 (F t x)).1 = 0 ↔ (J2 x).1 = 0) ∧
      (0 < (J2 (F t x)).2 ↔ 0 < (J2 x).2) ∧
      ((J2 (F t x)).2 = 0 ↔ (J2 x).2 = 0) := by
    have hf : Continuous (fun s : ℝ => J2 (F s x)) :=
      J2.continuous.comp (hF.continuous.comp (continuous_id.prodMk continuous_const))
    have hz : F 0 x = x := (hInitial 0 le_rfl x).1
    refine ⟨?_, (hZeros t x).1, ?_, (hZeros t x).2⟩
    · have hn (s : ℝ) : (J2 (F s x)).1 = 0 ↔ (J2 (F 0 x)).1 = 0 := by
        rw [hz]
        exact (hZeros s x).1
      simpa only [hz] using hContinuousSign _ hf.fst hn t
    · have hn (s : ℝ) : (J2 (F s x)).2 = 0 ↔ (J2 (F 0 x)).2 = 0 := by
        rw [hz]
        exact (hZeros s x).2
      simpa only [hz] using hContinuousSign _ hf.snd hn t
  exact ⟨F, hF, hFi, hFormula, hNorm, (fun t x ht => hInitial t ht x),
    (fun t x ht => hTerminal t ht x), hCompact, hSupport, hBranches, hSigns⟩

end PoincareConjecture.M25.Topology3D
