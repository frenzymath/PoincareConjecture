


import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Segment









set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves


noncomputable def secantAffineMap (f : ℝ → ℝ) (a b : ℝ) : ℝ →ᵃ[ℝ] ℝ where
  toFun t := f a + ((f b - f a) / (b - a)) * (t - a)
  linear := ((f b - f a) / (b - a)) • LinearMap.id
  map_vadd' := by
    intro t s
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

theorem secantAffineMap_eq_lineMap (f : ℝ → ℝ) (a b t : ℝ) :
    secantAffineMap f a b t =
      AffineMap.lineMap (f a) (f b) ((t - a) / (b - a)) := by
  simp only [secantAffineMap, AffineMap.coe_mk, AffineMap.lineMap_apply,
    smul_eq_mul, vadd_eq_add, vsub_eq_sub]
  ring

@[simp] theorem secantAffineMap_linear_one (f : ℝ → ℝ) (a b : ℝ) :
    (secantAffineMap f a b).linear 1 = (f b - f a) / (b - a) := by
  simp [secantAffineMap]



theorem exists_piecewiseAffine_approximation
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ) (piece : Fin n → ℝ →ᵃ[ℝ] ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      (∀ i, piece i (c i.castSucc) = f (c i.castSucc) ∧
        piece i (c i.succ) = f (c i.succ)) ∧
      (∀ i t, piece i t = f (c i.castSucc) +
        ((f (c i.succ) - f (c i.castSucc)) / (c i.succ - c i.castSucc)) *
          (t - c i.castSucc)) ∧
      (∀ i t, t ∈ Icc (c i.castSucc) (c i.succ) →
        |piece i t - f t| < ε ∧ |(piece i).linear 1 - deriv f t| < ε) := by
  have hfc : ContinuousOn f (Icc a b) := hf.continuousOn.mono hI
  have hdc : ContinuousOn (deriv f) (Icc a b) :=
    (hf.continuousOn_deriv_of_isOpen hU (by norm_num)).mono hI
  obtain ⟨δf, hδf, hcloseF⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hfc) ε hε
  obtain ⟨δd, hδd, hcloseD⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hdc) ε hε
  let δ := min δf δd
  have hδ : 0 < δ := lt_min hδf hδd
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
  have hc : StrictMono c := by
    intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    simpa only [c, add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right hcast hdpos) a
  have hca : c 0 = a := by simp [c]
  have hcb : c (Fin.last n) = b := by
    dsimp [c, d]
    field_simp
    ring
  have hcell (i : Fin n) : Icc (c i.castSucc) (c i.succ) ⊆ Icc a b := by
    intro t ht
    constructor
    · rw [← hca]
      exact (hc.monotone (Fin.zero_le i.castSucc)).trans ht.1
    · rw [← hcb]
      exact ht.2.trans (hc.monotone (Fin.le_last i.succ))
  have hstep (i : Fin n) : c i.succ - c i.castSucc = d := by
    simp only [c, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  have hdist (i : Fin n) {s t : ℝ}
      (hs : s ∈ Icc (c i.castSucc) (c i.succ))
      (ht : t ∈ Icc (c i.castSucc) (c i.succ)) : dist s t < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hstep i, hdδ, hs.1, hs.2, ht.1, ht.2]
  let piece (i : Fin n) := secantAffineMap f (c i.castSucc) (c i.succ)
  refine ⟨n, c, piece, by exact_mod_cast hnpos, hc, hca, hcb, ?_, fun _ _ => rfl, ?_⟩
  · intro i
    constructor
    · simp [piece, secantAffineMap]
    · change f (c i.castSucc) +
        ((f (c i.succ) - f (c i.castSucc)) / (c i.succ - c i.castSucc)) *
          (c i.succ - c i.castSucc) = f (c i.succ)
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (hc Fin.castSucc_lt_succ).ne')]
      ring
  · intro i t ht
    have hlt := hc (Fin.castSucc_lt_succ (i := i))
    have hleft : c i.castSucc ∈ Icc (c i.castSucc) (c i.succ) := left_mem_Icc.mpr hlt.le
    have hright : c i.succ ∈ Icc (c i.castSucc) (c i.succ) := right_mem_Icc.mpr hlt.le
    constructor
    · have hend {s : ℝ} (hs : s ∈ Icc (c i.castSucc) (c i.succ)) :
          f s ∈ Ioo (f t - ε) (f t + ε) := by
        have he := hcloseF s (hcell i hs) t (hcell i ht)
          ((hdist i hs ht).trans_le (min_le_left _ _))
        rw [Real.dist_eq, abs_lt] at he
        constructor <;> linarith [he.1, he.2]
      have hpiece : piece i t ∈ Ioo (f t - ε) (f t + ε) := by
        rw [show piece i t = AffineMap.lineMap (f (c i.castSucc)) (f (c i.succ))
          ((t - c i.castSucc) / (c i.succ - c i.castSucc)) from
            secantAffineMap_eq_lineMap f _ _ t]
        apply (convex_Ioo (f t - ε) (f t + ε)).lineMap_mem (hend hleft) (hend hright)
        have hp : 0 < c i.succ - c i.castSucc := sub_pos.mpr hlt
        exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hp.le,
          (div_le_one hp).mpr (sub_le_sub_right ht.2 _)⟩
      rw [abs_lt]
      constructor <;> linarith [hpiece.1, hpiece.2]
    · obtain ⟨s, hs, hslope⟩ := exists_deriv_eq_slope f hlt
        (hfc.mono (hcell i))
        ((hf.differentiableOn (by norm_num)).mono
          ((Ioo_subset_Icc_self.trans (hcell i)).trans hI))
      have he := hcloseD s (hcell i (Ioo_subset_Icc_self hs)) t (hcell i ht)
        ((hdist i (Ioo_subset_Icc_self hs) ht).trans_le (min_le_right _ _))
      simpa only [Real.dist_eq, hslope, piece, secantAffineMap_linear_one] using he

end Poincare.Topology.Plane.Curves
