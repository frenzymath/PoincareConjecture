import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Vertical
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Algebra.Structures















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing



theorem exists_scalar_collar_extension (h : RoundCylinderSpace → ℝ)
    (hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h)
    (hpos : ∀ q : UnitTwoSphere, 0 < deriv (fun t : ℝ => h (q, t)) 0) :
    ∃ (r : ℝ) (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → F (q, t) = (q, h (q, t)) := by
  have haxial (f : RoundCylinderSpace → ℝ)
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
  let α : UnitTwoSphere → ℝ := fun q => deriv (fun t : ℝ => h (q, t)) 0
  let β : UnitTwoSphere → ℝ := fun q => h (q, 0)
  have hαpos (q : UnitTwoSphere) : 0 < α q := hpos q
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ α :=
    (haxial h hh).comp (contMDiff_id.prodMk contMDiff_const)
  have hβ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ β :=
    hh.comp (contMDiff_id.prodMk contMDiff_const)
  let e : RoundCylinderSpace → ℝ := fun p => (h p - β p.1) / α p.1 - p.2
  have he : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ e :=
    ((hh.sub (hβ.comp contMDiff_fst)).div₀ (hα.comp contMDiff_fst)
      (fun p => (hpos p.1).ne')).sub contMDiff_snd
  have he0 (q : UnitTwoSphere) : e (q, 0) = 0 := by simp [e, β]
  have he1 (q : UnitTwoSphere) : deriv (fun t : ℝ => e (q, t)) 0 = 0 := by
    have hdh : HasDerivAt (fun t : ℝ => h (q, t)) (α q) 0 :=
      (((hh.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable
        (by simp)) 0).hasDerivAt
    have hd := ((hdh.sub_const (β q)).div_const (α q)).sub (hasDerivAt_id (0 : ℝ))
    have hde := hd.deriv
    change deriv (fun t => e (q, t)) 0 = α q / α q - 1 at hde
    rw [div_self (hαpos q).ne', sub_self] at hde
    exact hde
  let a : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have ha : ContDiff ℝ ∞ (a : ℝ → ℝ) := a.contDiff
  obtain ⟨C, hC⟩ := a.hasCompactSupport.deriv.exists_bound_of_continuous
    (ha.continuous_deriv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let δ := (2 * (C + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let U : Set RoundCylinderSpace :=
    {p | |deriv (fun t : ℝ => e (p.1, t)) p.2| < δ}
  have hU : IsOpen U := isOpen_lt ((haxial e he).continuous.abs) continuous_const
  have hzero : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    change |deriv (fun t : ℝ => e (q, t)) 0| < δ
    rw [he1, abs_zero]
    exact hδ
  obtain ⟨u, v, _, hv, hu, hz, huv⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) hU hzero
  obtain ⟨d, hd, hdv⟩ := Metric.isOpen_iff.mp hv 0 (hz (by simp))
  have hed (q : UnitTwoSphere) (t : ℝ) (ht : |t| < d) :
      |deriv (fun s : ℝ => e (q, s)) t| ≤ δ := by
    have hqt : (q, t) ∈ U := huv ⟨hu (mem_univ q),
      hdv (by simpa [Metric.mem_ball, Real.dist_eq] using ht)⟩
    exact hqt.le
  let r := d / 2
  have hr : 0 < r := half_pos hd
  have hrd : r < d := half_lt_self hd
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
  let L : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ := {
    toFun := fun p => (p.1, α p.1 * p.2 + β p.1)
    invFun := fun p => (p.1, (p.2 - β p.1) / α p.1)
    left_inv := by
      intro p
      refine Prod.ext rfl ?_
      dsimp
      field_simp [(hαpos p.1).ne']; ring
    right_inv := by
      intro p
      refine Prod.ext rfl ?_
      dsimp
      field_simp [(hαpos p.1).ne']; ring
    contMDiff_toFun := contMDiff_fst.prodMk
      (((hα.comp contMDiff_fst).mul contMDiff_snd).add (hβ.comp contMDiff_fst))
    contMDiff_invFun := contMDiff_fst.prodMk
      ((contMDiff_snd.sub (hβ.comp contMDiff_fst)).div₀
        (hα.comp contMDiff_fst) (fun p => (hpos p.1).ne')) }
  refine ⟨r / 2, K.trans L, half_pos hr, ?_, ?_⟩
  · intro p
    change (K p).1 = p.1
    rw [hK]
  · intro q t ht
    change L (K (q, t)) = (q, h (q, t))
    rw [hK]
    refine Prod.ext ?_ ?_
    · rfl
    change α q * (t + b t * ((h (q, t) - β q) / α q - t)) + β q = h (q, t)
    rw [hb1 t ht, one_mul]
    field_simp [(hαpos q).ne']; ring

end PoincareConjecture.CylinderGluing
