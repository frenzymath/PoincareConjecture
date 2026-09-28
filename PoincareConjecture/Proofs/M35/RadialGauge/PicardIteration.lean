import PoincareConjecture.Proofs.M35.RadialGauge.PicardContraction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem gaugePicard_weighted_c1_bound
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {eta B L C T : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hm : ∀ k, StronglyMeasurable (fun p : ℝ × V =>
      gaugeSource (b p.1) (G p.1) (gaugePicard b G k p.1) p.2))
    (hr : ∀ k s, s ∈ Icc 0 T → ContDiff ℝ 1 (gaugeSource (b s) (G s) (gaugePicard b G k s)))
    (hbr : ∀ k s, s ∈ Ico 0 T → ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ D)
    (hsmall : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) T ≤ eta) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G k t x‖ ≤ eta ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta := by
  have hS : 0 ≤ B * eta + eta ^ 2 + L * eta + C := by positivity
  intro k
  induction k with
  | zero =>
    intro t ht x
    constructor <;> simpa [gaugePicard] using heta
  | succ k ih =>
    intro t ht x
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hsub' : Ico 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
    have hsrc := gaugeSource_weighted_bound heta hB hL
      (fun s hs => hb s (hsub hs)) (fun s hs => hGzero s (hsub hs))
      (fun s hs => hGlip s (hsub hs))
      (fun s hs y => by simpa only [Real.norm_eq_abs] using (ih s (hsub hs) y).1)
      (fun s hs y => (ih s (hsub hs) y).2)
    have h := heatDuhamel_c1_bound hS ht.1 (hm k)
      (fun s hs => hr k s (hsub hs)) (fun s hs => hbr k s (hsub' hs)) hsrc x
    have hgain : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) t ≤ eta :=
      (mul_le_mul_of_nonneg_left (heatC1Gain_mono ht.1 ht.2) hS).trans hsmall
    exact ⟨h.1.trans hgain, h.2.trans hgain⟩



theorem gaugePicard_weighted_c1_geometric
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {eta B L C T : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hm : ∀ k, StronglyMeasurable (fun p : ℝ × V =>
      gaugeSource (b p.1) (G p.1) (gaugePicard b G k p.1) p.2))
    (hr : ∀ k s, s ∈ Icc 0 T → ContDiff ℝ 1 (gaugeSource (b s) (G s) (gaugePicard b G k s)))
    (hbr : ∀ k s, s ∈ Ico 0 T → ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ D)
    (hsmall : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) T ≤ eta)
    (hcontract : (L + B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 2) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G (k + 1) t x - gaugePicard b G k t x‖ ≤
        eta * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G (k + 1) t) x -
        fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta * (1 / 2 : ℝ) ^ k := by
  have hball := gaugePicard_weighted_c1_bound heta hB hL hC hb hGzero hGlip hm hr hbr hsmall
  have hK : 0 ≤ L + B + 2 * eta := by positivity
  intro k
  induction k with
  | zero =>
    intro t ht x
    simpa [gaugePicard] using hball 1 t ht x
  | succ k ih =>
    intro t ht x
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hsub' : Ico 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
    have hd : 0 ≤ eta * (1 / 2 : ℝ) ^ k := by positivity
    have h := gaugeDuhamel_c1_difference_bound heta hB hL hC hd ht.1
      (fun s hs => hb s (hsub hs)) (fun s hs => hGzero s (hsub hs))
      (fun s hs => hGlip s (hsub hs))
      (fun s hs y => by simpa only [Real.norm_eq_abs] using (hball (k + 1) s (hsub hs) y).1)
      (fun s hs y => by simpa only [Real.norm_eq_abs] using (hball k s (hsub hs) y).1)
      (fun s hs y => (hball (k + 1) s (hsub hs) y).2)
      (fun s hs y => (hball k s (hsub hs) y).2)
      (fun s hs y => by simpa only [Real.norm_eq_abs] using (ih s (hsub hs) y).1)
      (fun s hs y => (ih s (hsub hs) y).2)
      (hm (k + 1)) (hm k) (fun s hs => hr (k + 1) s (hsub hs))
      (fun s hs => hr k s (hsub hs)) (fun s hs => hbr (k + 1) s (hsub' hs))
      (fun s hs => hbr k s (hsub' hs)) x
    have hgain : (L + B + 2 * eta) * (eta * (1 / 2 : ℝ) ^ k) * heatC1Gain (n + 1) t ≤
        eta * (1 / 2 : ℝ) ^ (k + 1) := by
      calc
        _ = ((L + B + 2 * eta) * heatC1Gain (n + 1) t) * (eta * (1 / 2 : ℝ) ^ k) := by ring
        _ ≤ ((L + B + 2 * eta) * heatC1Gain (n + 1) T) * (eta * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (heatC1Gain_mono ht.1 ht.2) hK) hd
        _ ≤ (1 / 2) * (eta * (1 / 2 : ℝ) ^ k) := mul_le_mul_of_nonneg_right hcontract hd
        _ = _ := by rw [pow_succ]; ring
    exact ⟨h.1.trans hgain, h.2.trans hgain⟩

end PoincareConjecture.M35.RadialGauge
