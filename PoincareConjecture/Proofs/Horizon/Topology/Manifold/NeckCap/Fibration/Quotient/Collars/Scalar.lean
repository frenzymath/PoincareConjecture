import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing

theorem contMDiff_axial_deriv (f : RoundCylinderSpace → ℝ)
    (hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : RoundCylinderSpace => deriv (fun t : ℝ => f (p.1, t)) p.2) := by
  intro p
  let a : RoundCylinderSpace → ℝ → ℝ := fun z t => f (z.1, t)
  have ha : ContMDiff (((𝓡 2).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry a) :=
    hf.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)
  have hd := ha.contMDiffAt.mfderiv a Prod.snd
    (contMDiff_snd.contMDiffAt (x := p)) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  rw [inTangentCoordinates_model_space] at hd
  have hv := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  simpa only [mfderiv_eq_fderiv, fderiv_eq_deriv_mul, mul_one, a] using hv



theorem exists_supported_scalar_extension_threshold :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : RoundCylinderSpace → ℝ),
      ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h →
      (∀ q : UnitTwoSphere, h (q, 0) = 0) →
      (∀ q : UnitTwoSphere, |deriv (fun t : ℝ => h (q, t)) 0 - 1| < δ) →
      ∀ R : ℝ, 0 < R →
      ∃ (r : ℝ) (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
          ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
        0 < r ∧ r < R ∧ (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
        (∀ p : RoundCylinderSpace, R ≤ |p.2| → F p = p) ∧
        ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → F (q, t) = (q, h (q, t)) := by
  let a : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have ha : ContDiff ℝ ∞ (a : ℝ → ℝ) := a.contDiff
  obtain ⟨C, hC⟩ := a.hasCompactSupport.deriv.exists_bound_of_continuous
    (ha.continuous_deriv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let δ := (2 * (C + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro h hh hh0 hh1 R hR
  let e : RoundCylinderSpace → ℝ := fun p => h p - p.2
  have he : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ e := hh.sub contMDiff_snd
  have he0 (q : UnitTwoSphere) : e (q, 0) = 0 := by simp [e, hh0]
  have he1 (q : UnitTwoSphere) : |deriv (fun t : ℝ => e (q, t)) 0| < δ := by
    have hdh : HasDerivAt (fun t : ℝ => h (q, t)) (deriv (fun t => h (q, t)) 0) 0 :=
      (((hh.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable
        (by simp)) 0).hasDerivAt
    have hd := (hdh.sub (hasDerivAt_id (0 : ℝ))).deriv
    change deriv (fun t => e (q, t)) 0 = deriv (fun t => h (q, t)) 0 - 1 at hd
    rw [hd]
    exact hh1 q
  let U : Set RoundCylinderSpace :=
    {p | |deriv (fun t : ℝ => e (p.1, t)) p.2| < δ}
  have hU : IsOpen U := isOpen_lt ((contMDiff_axial_deriv e he).continuous.abs) continuous_const
  have hzero : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact he1 q
  obtain ⟨u, v, _, hv, hu, hz, huv⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) hU hzero
  obtain ⟨d, hd, hdv⟩ := Metric.isOpen_iff.mp hv 0 (hz (by simp))
  have hed (q : UnitTwoSphere) (t : ℝ) (ht : |t| < d) :
      |deriv (fun s : ℝ => e (q, s)) t| ≤ δ := by
    have hqt : (q, t) ∈ U := huv ⟨hu (mem_univ q),
      hdv (by simpa [Metric.mem_ball, Real.dist_eq] using ht)⟩
    exact hqt.le
  let r := min d R / 2
  have hr : 0 < r := half_pos (lt_min hd hR)
  have hrd : r < d := (half_lt_self (lt_min hd hR)).trans_le (min_le_left _ _)
  have hrR : r < R := (half_lt_self (lt_min hd hR)).trans_le (min_le_right _ _)
  let b : ℝ → ℝ := fun t => a (t / r)
  have hb : ContDiff ℝ ∞ b := ha.comp (contDiff_id.div_const r)
  have hb0 (t : ℝ) (ht : r ≤ |t|) : b t = 0 := by
    apply a.zero_of_le_dist
    change 1 ≤ dist (t / r) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hr]
    exact (le_div_iff₀ hr).mpr (by simpa using ht)
  have hb1 (t : ℝ) (ht : |t| < r / 2) : b t = 1 := by
    apply a.one_of_mem_closedBall
    change dist (t / r) 0 ≤ 1 / 2
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by linarith)
  have hbd (t : ℝ) : |deriv b t| ≤ C / r := by
    have hd := ((ha.differentiable (by simp) (t / r)).hasDerivAt).comp t
      ((hasDerivAt_id t).div_const r)
    have heq : deriv b t = deriv a (t / r) / r := by
      convert hd.deriv using 1 <;> simp [b, div_eq_mul_inv, Function.comp_def]
    rw [heq, abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using hC (t / r)) hr.le
  have hebound (q : UnitTwoSphere) (t : ℝ) (ht : |t| ≤ r) : |e (q, t)| ≤ δ * r := by
    have hdiff : ∀ t ∈ Metric.ball (0 : ℝ) d,
        DifferentiableAt ℝ (fun s => e (q, s)) t := fun t _ =>
      ((he.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable (by simp)) t
    have hbound : ∀ t ∈ Metric.ball (0 : ℝ) d,
        ‖deriv (fun s => e (q, s)) t‖ ≤ δ := by
      intro t ht
      exact hed q t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
    have hmv := (convex_ball (0 : ℝ) d).norm_image_sub_le_of_norm_deriv_le
      hdiff hbound (Metric.mem_ball_self hd)
      (show t ∈ Metric.ball (0 : ℝ) d by
        simpa [Metric.mem_ball, Real.dist_eq] using ht.trans_lt hrd)
    rw [he0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    exact hmv.trans (mul_le_mul_of_nonneg_left ht hδ.le)
  let k : RoundCylinderSpace → ℝ := fun p => p.2 + b p.2 * e p
  have hk : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ k :=
    contMDiff_snd.add ((hb.contMDiff.comp contMDiff_snd).mul he)
  have hkderiv (q : UnitTwoSphere) (t : ℝ) :
      HasDerivAt (fun s => k (q, s))
        (1 + (deriv b t * e (q, t) + b t * deriv (fun s => e (q, s)) t)) t := by
    exact (hasDerivAt_id t).add (((hb.differentiable (by simp) t).hasDerivAt).mul
      (((he.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable
        (by simp) t).hasDerivAt))
  have hkeq (q : UnitTwoSphere) (t : ℝ) (ht : r ≤ |t|) : k (q, t) = t := by
    simp [k, hb0 t ht]
  have hkpos (q : UnitTwoSphere) (t : ℝ) : 0 < deriv (fun s => k (q, s)) t := by
    by_cases ht : |t| ≤ r
    · have herror : |deriv b t * e (q, t) + b t * deriv (fun s => e (q, s)) t| ≤ 1 / 2 := by
        calc
          _ ≤ |deriv b t| * |e (q, t)| + |b t| * |deriv (fun s => e (q, s)) t| :=
            (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
          _ ≤ (C / r) * (δ * r) + 1 * δ := by
            exact add_le_add
              (mul_le_mul (hbd t) (hebound q t ht) (abs_nonneg _) (div_nonneg hC0 hr.le))
              (mul_le_mul
                (by simpa only [b, abs_of_nonneg a.nonneg] using a.le_one (x := t / r))
                (hed q t (ht.trans_lt hrd)) (abs_nonneg _) zero_le_one)
          _ = 1 / 2 := by
            dsimp [δ]
            field_simp [hr.ne', ne_of_gt (show 0 < C + 1 by linarith)]
      rw [(hkderiv q t).deriv]
      have hl := (abs_le.mp herror).1
      linarith
    · have hloc : (fun s => k (q, s)) =ᶠ[𝓝 t] id := by
        have hn : ∀ᶠ z in 𝓝 t, r < |z| := continuous_abs.continuousAt.eventually
          (lt_mem_nhds (lt_of_not_ge ht))
        filter_upwards [hn] with z hz using hkeq q z hz.le
      rw [((hasDerivAt_id t).congr_of_eventuallyEq hloc).deriv]
      norm_num
  have hksurj (q : UnitTwoSphere) : Function.Surjective (fun t : ℝ => k (q, t)) := by
    intro y
    let T := r + |y| + 1
    have hT : 0 < T := by dsimp [T]; positivity
    have hrT : r ≤ T := by dsimp [T]; linarith [abs_nonneg y]
    have hneg : k (q, -T) = -T :=
      hkeq q (-T) (by simpa [abs_neg, abs_of_pos hT] using hrT)
    have hplus : k (q, T) = T := hkeq q T (by simpa [abs_of_pos hT] using hrT)
    have hy : y ∈ Icc (k (q, -T)) (k (q, T)) := by
      rw [hneg, hplus]
      constructor <;> dsimp [T] <;> linarith [neg_abs_le y, le_abs_self y]
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (neg_le_self hT.le)
      (hk.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn hy
    exact ⟨t, ht⟩
  obtain ⟨K, hK⟩ := exists_vertical_diffeomorph k hk
    (fun q => ⟨(strictMono_of_deriv_pos (hkpos q)).injective, hksurj q⟩)
    (fun p => ⟨deriv (fun t => k (p.1, t)) p.2, (hkpos p.1 p.2).ne',
      (((hk.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable
        (by simp)) p.2).hasDerivAt⟩)
  refine ⟨r / 2, K, half_pos hr, (half_lt_self hr).trans hrR, ?_, ?_, ?_⟩
  · intro p
    rw [hK]
  · rintro ⟨q, t⟩ ht
    rw [hK, hkeq q t (hrR.le.trans ht)]
  · intro q t ht
    rw [hK]
    simp only [k, hb1 t ht, one_mul, e]
    congr 1
    ring

theorem exists_uniform_collar_bound (h : RoundCylinderSpace → ℝ)
    (hh : Continuous h) (hzero : ∀ q : UnitTwoSphere, h (q, 0) = 0)
    {s : ℝ} (hs : 0 < s) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : UnitTwoSphere, ∀ t : ℝ, |t| < r → |h (q, t)| < s := by
  let U : Set RoundCylinderSpace := {p | |h p| < s}
  have hU : IsOpen U := isOpen_lt hh.abs continuous_const
  have hzeroU : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    change |h (q, 0)| < s
    simpa [hzero] using hs
  obtain ⟨u, v, _, hv, hu, hz, huv⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) hU hzeroU
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hv 0 (hz (by simp))
  refine ⟨r, hr, ?_⟩
  intro q t ht
  exact huv ⟨hu (mem_univ q), hrv (by simpa [Metric.mem_ball, Real.dist_eq] using ht)⟩



theorem exists_small_smooth_positive_root (α : UnitTwoSphere → ℝ)
    (hα : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ α) (hpos : ∀ q, 0 < α q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (β : UnitTwoSphere → ℝ),
      0 < n ∧ ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ β ∧
      (∀ q, 0 < β q) ∧ (∀ q, |β q - 1| < δ) ∧ (∀ q, β q ^ n = α q) := by
  have hlog : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun q => Real.log (α q)) := by
    intro q
    exact (Real.contDiffAt_log.mpr (hpos q).ne').comp_contMDiffAt (hα q)
  let e : RoundCylinderSpace → ℝ := fun p => Real.exp (p.2 * Real.log (α p.1)) - 1
  have he : Continuous e :=
    (Real.continuous_exp.comp (continuous_snd.mul (hlog.continuous.comp continuous_fst))).sub
      continuous_const
  obtain ⟨d, hd, hde⟩ := exists_uniform_collar_bound e he (by intro q; simp [e]) hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
  let β : UnitTwoSphere → ℝ := fun q => Real.exp (Real.log (α q) / (n + 1 : ℝ))
  have hβ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ β :=
    Real.contDiff_exp.contMDiff.comp (hlog.div_const (n + 1 : ℝ))
  refine ⟨n + 1, β, Nat.succ_pos n, hβ, fun q => Real.exp_pos _, ?_, ?_⟩
  · intro q
    have h := hde q (1 / (n + 1 : ℝ)) (by rw [abs_of_pos (by positivity)]; exact hn)
    simpa only [e, β, one_div, div_eq_mul_inv, one_mul, mul_comm] using h
  · intro q
    dsimp [β]
    rw [← Real.exp_nat_mul]
    have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_add, Nat.cast_one, mul_div_cancel₀ _ hn0, Real.exp_log (hpos q)]


theorem exists_supported_scaling_extension (α : UnitTwoSphere → ℝ)
    (hα : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ α) (hpos : ∀ q, 0 < α q)
    (R : ℝ) (hR : 0 < R) :
    ∃ (r : ℝ) (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ r < R ∧ (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, R ≤ |p.2| → F p = p) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → F (q, t) = (q, α q * t) := by
  obtain ⟨δ, hδ, hext⟩ := exists_supported_scalar_extension_threshold
  obtain ⟨N, β, _, hβ, _, hsmall, hpow⟩ := exists_small_smooth_positive_root α hα hpos hδ
  obtain ⟨s, K, hs, hsR, hKfst, hKout, hKlocal⟩ :=
    hext (fun p => β p.1 * p.2) ((hβ.comp contMDiff_fst).mul contMDiff_snd)
      (by intro q; simp) (by intro q; simpa using hsmall q) R hR
  have hiter : ∀ n : ℕ, ∃ (r : ℝ) (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ r < R ∧ (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, R ≤ |p.2| → F p = p) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → F (q, t) = (q, β q ^ n * t) := by
    intro n
    induction n with
    | zero =>
      refine ⟨R / 2, Diffeomorph.refl _ _ _, half_pos hR, half_lt_self hR,
        fun _ => rfl, fun _ _ => rfl, ?_⟩
      intro q t _
      simp
    | succ n ih =>
      obtain ⟨r, F, hr, hrR, hFfst, hFout, hFlocal⟩ := ih
      have hpowcont : Continuous (fun p : RoundCylinderSpace => β p.1 ^ n * p.2) :=
        ((hβ.continuous.comp continuous_fst).pow n).mul continuous_snd
      obtain ⟨d, hd, hdlocal⟩ := exists_uniform_collar_bound
        (fun p : RoundCylinderSpace => β p.1 ^ n * p.2) hpowcont (by intro q; simp) hs
      refine ⟨min r d, F.trans K, lt_min hr hd, (min_le_left _ _).trans_lt hrR,
        ?_, ?_, ?_⟩
      · intro p
        change (K (F p)).1 = p.1
        rw [hKfst, hFfst]
      · intro p hp
        change K (F p) = p
        rw [hFout p hp, hKout p hp]
      · intro q t ht
        change K (F (q, t)) = _
        rw [hFlocal q t (ht.trans_le (min_le_left _ _)),
          hKlocal q (β q ^ n * t) (hdlocal q t (ht.trans_le (min_le_right _ _)))]
        congr 1
        ring
  obtain ⟨r, F, hr, hrR, hFfst, hFout, hFlocal⟩ := hiter N
  exact ⟨r, F, hr, hrR, hFfst, hFout, by simpa only [hpow] using hFlocal⟩



theorem exists_supported_scalar_collar_extension (h : RoundCylinderSpace → ℝ)
    (hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h)
    (hzero : ∀ q : UnitTwoSphere, h (q, 0) = 0)
    (hpos : ∀ q : UnitTwoSphere, 0 < deriv (fun t : ℝ => h (q, t)) 0)
    (R : ℝ) (hR : 0 < R) :
    ∃ (r : ℝ) (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ r < R ∧ (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, R ≤ |p.2| → F p = p) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → F (q, t) = (q, h (q, t)) := by
  let α : UnitTwoSphere → ℝ := fun q => deriv (fun t : ℝ => h (q, t)) 0
  have hαpos (q : UnitTwoSphere) : 0 < α q := hpos q
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ α :=
    (contMDiff_axial_deriv h hh).comp (contMDiff_id.prodMk contMDiff_const)
  let e : RoundCylinderSpace → ℝ := fun p => h p / α p.1
  have he : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ e :=
    hh.div₀ (hα.comp contMDiff_fst) (fun p => (hαpos p.1).ne')
  have he0 (q : UnitTwoSphere) : e (q, 0) = 0 := by simp [e, hzero]
  have he1 (q : UnitTwoSphere) : deriv (fun t : ℝ => e (q, t)) 0 = 1 := by
    have hd : HasDerivAt (fun t : ℝ => h (q, t)) (α q) 0 :=
      (((hh.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable
        (by simp)) 0).hasDerivAt
    simpa only [div_self (hαpos q).ne'] using (hd.div_const (α q)).deriv
  obtain ⟨δ, hδ, hext⟩ := exists_supported_scalar_extension_threshold
  obtain ⟨r, K, hr, hrR, hKfst, hKout, hKlocal⟩ :=
    hext e he he0 (by intro q; simpa only [he1, sub_self, abs_zero] using hδ) R hR
  obtain ⟨s, L, hs, _, hLfst, hLout, hLlocal⟩ :=
    exists_supported_scaling_extension α hα hαpos R hR
  obtain ⟨d, hd, hde⟩ := exists_uniform_collar_bound e he.continuous he0 hs
  refine ⟨min r d, K.trans L, lt_min hr hd, (min_le_left _ _).trans_lt hrR,
    ?_, ?_, ?_⟩
  · intro p
    change (L (K p)).1 = p.1
    rw [hLfst, hKfst]
  · intro p hp
    change L (K p) = p
    rw [hKout p hp, hLout p hp]
  · intro q t ht
    change L (K (q, t)) = _
    rw [hKlocal q t (ht.trans_le (min_le_left _ _)),
      hLlocal q (e (q, t)) (hde q t (ht.trans_le (min_le_right _ _)))]
    congr 1
    exact mul_div_cancel₀ _ (hαpos q).ne'

end PoincareConjecture.CylinderGluing
