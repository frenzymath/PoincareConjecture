


import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor









set_option autoImplicit false

open Set Metric

namespace Poincare.Topology.Plane.Curves

private theorem exists_continuous_between_with_endpoints
    {lo hi : ℝ → ℝ} {a b ya yb : ℝ} (hab : a < b)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hgap : ∀ t ∈ Icc a b, lo t < hi t)
    (ha : lo a < ya ∧ ya < hi a) (hb : lo b < yb ∧ yb < hi b) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc a b) ∧ g a = ya ∧ g b = yb ∧
      ∀ t ∈ Icc a b, lo t < g t ∧ g t < hi t := by
  let α := (ya - lo a) / (hi a - lo a)
  let β := (yb - lo b) / (hi b - lo b)
  have ha' : 0 < hi a - lo a := sub_pos.mpr (ha.1.trans ha.2)
  have hb' : 0 < hi b - lo b := sub_pos.mpr (hb.1.trans hb.2)
  have hα : α ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ha.1) ha', (div_lt_one ha').mpr (sub_lt_sub_right ha.2 _)⟩
  have hβ : β ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hb.1) hb', (div_lt_one hb').mpr (sub_lt_sub_right hb.2 _)⟩
  let θ (t : ℝ) := AffineMap.lineMap α β ((t - a) / (b - a))
  have hθ : Continuous θ := by
    unfold θ
    simp only [AffineMap.lineMap_apply, smul_eq_mul, vadd_eq_add]
    fun_prop
  have hθbounds (t : ℝ) (ht : t ∈ Icc a b) : θ t ∈ Ioo (0 : ℝ) 1 := by
    apply (convex_Ioo (0 : ℝ) 1).lineMap_mem hα hβ
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2 _)⟩
  let g (t : ℝ) := lo t + θ t * (hi t - lo t)
  refine ⟨g, hlo.add (hθ.continuousOn.mul (hhi.sub hlo)), ?_, ?_, ?_⟩
  · dsimp [g, θ]
    simp only [sub_self, zero_div, AffineMap.lineMap_apply_zero]
    dsimp [α]
    rw [div_mul_cancel₀ _ ha'.ne']
    ring
  · dsimp [g, θ]
    rw [div_self (sub_pos.mpr hab).ne', AffineMap.lineMap_apply_one]
    dsimp [β]
    rw [div_mul_cancel₀ _ hb'.ne']
    ring
  · intro t ht
    have hθt := hθbounds t ht
    have hgt := sub_pos.mpr (hgap t ht)
    dsimp [g]
    constructor
    · exact lt_add_of_pos_right _ (mul_pos hθt.1 hgt)
    · nlinarith [mul_pos (sub_pos.mpr hθt.2) hgt]

private noncomputable def affineInterpolation (a b u v : ℝ) : ℝ →ᵃ[ℝ] ℝ where
  toFun t := u + ((v - u) / (b - a)) * (t - a)
  linear := ((v - u) / (b - a)) • LinearMap.id
  map_vadd' := by
    intro t s
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

private theorem affineInterpolation_eq_lineMap (a b u v t : ℝ) :
    affineInterpolation a b u v t = AffineMap.lineMap u v ((t - a) / (b - a)) := by
  simp only [affineInterpolation, AffineMap.coe_mk, AffineMap.lineMap_apply,
    smul_eq_mul, vadd_eq_add, vsub_eq_sub]
  ring





theorem exists_piecewiseAffine_between
    {lo hi : ℝ → ℝ} {a b ya yb : ℝ} (hab : a < b)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hgap : ∀ t ∈ Icc a b, lo t < hi t)
    (ha : lo a < ya ∧ ya < hi a) (hb : lo b < yb ∧ yb < hi b) :
    ∃ (n : ℕ) (c y : Fin (n + 1) → ℝ) (piece : Fin n → ℝ →ᵃ[ℝ] ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      y 0 = ya ∧ y (Fin.last n) = yb ∧
      (∀ i, piece i (c i.castSucc) = y i.castSucc ∧ piece i (c i.succ) = y i.succ) ∧
      (∀ i t, piece i t = y i.castSucc +
        ((y i.succ - y i.castSucc) / (c i.succ - c i.castSucc)) * (t - c i.castSucc)) ∧
      (∀ i t, t ∈ Icc (c i.castSucc) (c i.succ) → lo t < piece i t ∧ piece i t < hi t) := by
  obtain ⟨g, hg, hga, hgb, hgbounds⟩ :=
    exists_continuous_between_with_endpoints hab hlo hhi hgap ha hb
  obtain ⟨η, hη, hclearance⟩ := isCompact_Icc.exists_forall_le'
    ((hg.sub hlo).inf (hhi.sub hg))
    (fun t ht => lt_min (sub_pos.mpr (hgbounds t ht).1)
      (sub_pos.mpr (hgbounds t ht).2))
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hnpos : (0 : ℝ) < n := (div_pos (sub_pos.mpr hab) hδ).trans hn
  have hnzero : (n : ℝ) ≠ 0 := hnpos.ne'
  let d : ℝ := (b - a) / n
  have hdpos : 0 < d := div_pos (sub_pos.mpr hab) hnpos
  have hdδ : d < δ := by
    apply (div_lt_iff₀ hnpos).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  let c (i : Fin (n + 1)) : ℝ := a + (i : ℝ) * d
  have hcmono : StrictMono c := by
    intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    simpa only [c, add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right hcast hdpos) a
  have hczero : c 0 = a := by simp [c]
  have hclast : c (Fin.last n) = b := by
    dsimp [c, d]
    field_simp
    ring
  have hcbounds (i : Fin (n + 1)) : c i ∈ Icc a b := by
    constructor
    · rw [← hczero]
      exact hcmono.monotone (Fin.zero_le i)
    · rw [← hclast]
      exact hcmono.monotone (Fin.le_last i)
  have hstep (i : Fin n) : c i.succ - c i.castSucc = d := by
    simp only [c, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  let piece (i : Fin n) :=
    affineInterpolation (c i.castSucc) (c i.succ) (g (c i.castSucc)) (g (c i.succ))
  refine ⟨n, c, g ∘ c, piece, by exact_mod_cast hnpos, hcmono, hczero, hclast,
    by simpa only [Function.comp_apply, hczero] using hga,
    by simpa only [Function.comp_apply, hclast] using hgb, ?_, fun _ _ => rfl, ?_⟩
  · intro i
    have hne : c i.succ ≠ c i.castSucc := (hcmono Fin.castSucc_lt_succ).ne'
    constructor
    · simp [piece, affineInterpolation]
    · change g (c i.castSucc) +
        ((g (c i.succ) - g (c i.castSucc)) / (c i.succ - c i.castSucc)) *
          (c i.succ - c i.castSucc) = g (c i.succ)
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hne)]
      ring
  · intro i t ht
    have htI : t ∈ Icc a b :=
      ⟨(hcbounds i.castSucc).1.trans ht.1, ht.2.trans (hcbounds i.succ).2⟩
    have hvalues (j : Fin (n + 1)) (hj : dist (c j) t < δ) :
        g (c j) ∈ Ioo (lo t) (hi t) := by
      have hdist := hclose (c j) (hcbounds j) t htI hj
      rw [Real.dist_eq, abs_lt] at hdist
      have hlow : η ≤ g t - lo t := (hclearance t htI).trans (min_le_left _ _)
      have hupp : η ≤ hi t - g t := (hclearance t htI).trans (min_le_right _ _)
      constructor <;> linarith [hdist.1, hdist.2]
    have hleft : g (c i.castSucc) ∈ Ioo (lo t) (hi t) := by
      apply hvalues
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.1)]
      linarith [hstep i, ht.2]
    have hright : g (c i.succ) ∈ Ioo (lo t) (hi t) := by
      apply hvalues
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [hstep i, ht.1]
    rw [show piece i t = AffineMap.lineMap (g (c i.castSucc)) (g (c i.succ))
      ((t - c i.castSucc) / (c i.succ - c i.castSucc)) from affineInterpolation_eq_lineMap _ _ _ _ _]
    apply (convex_Ioo (lo t) (hi t)).lineMap_mem hleft hright
    have hpos : 0 < c i.succ - c i.castSucc := sub_pos.mpr (hcmono Fin.castSucc_lt_succ)
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hpos.le,
      (div_le_one hpos).mpr (sub_le_sub_right ht.2 _)⟩

end Poincare.Topology.Plane.Curves
