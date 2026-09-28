import PoincareConjecture.Proofs.M35.RadialGauge.PicardContraction
import PoincareConjecture.Proofs.M35.RadialGauge.SlabSourceExtension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem heatDuhamel_c1_difference_bound_on_slab {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → V → F} {C D H T t : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hH : 0 ≤ H) (ht : t ∈ Icc 0 T)
    (hfm : StronglyMeasurable (fun p : Icc (0 : ℝ) T × V => f p.1 p.2))
    (hgm : StronglyMeasurable (fun p : Icc (0 : ℝ) T × V => g p.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (f s))
    (hg : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (g s))
    (hdf : ∀ s ∈ Ico 0 t, ∃ B : ℝ, ∀ x, ‖fderiv ℝ (f s) x‖ ≤ B)
    (hdg : ∀ s ∈ Ico 0 t, ∃ B : ℝ, ∀ x, ‖fderiv ℝ (g s) x‖ ≤ B)
    (hfb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C)
    (hgb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖g s x‖ ≤ D)
    (hfg : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x - g s x‖ ≤ H) (x : V) :
    (1 + ‖x‖) * ‖heatDuhamel f t x - heatDuhamel g t x‖ ≤ H * heatC1Gain (n + 1) t ∧
    (1 + ‖x‖) * ‖fderiv ℝ (heatDuhamel f t) x - fderiv ℝ (heatDuhamel g t) x‖ ≤
      H * heatC1Gain (n + 1) t := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have h := heatDuhamel_c1_difference_bound hC hD hH ht.1
    (slabSourceExtension_stronglyMeasurable hfm) (slabSourceExtension_stronglyMeasurable hgm)
    (fun s hs => by rw [slabSourceExtension_of_mem (hsub hs)]; exact hf s hs)
    (fun s hs => by rw [slabSourceExtension_of_mem (hsub hs)]; exact hg s hs)
    (fun s hs => by rw [slabSourceExtension_of_mem (hsub ⟨hs.1, hs.2.le⟩)]; exact hdf s hs)
    (fun s hs => by rw [slabSourceExtension_of_mem (hsub ⟨hs.1, hs.2.le⟩)]; exact hdg s hs)
    (fun s hs y => by rw [slabSourceExtension_of_mem (hsub hs)]; exact hfb s hs y)
    (fun s hs y => by rw [slabSourceExtension_of_mem (hsub hs)]; exact hgb s hs y)
    (fun s hs y => by rw [slabSourceExtension_of_mem (hsub hs),
      slabSourceExtension_of_mem (hsub hs)]; exact hfg s hs y) x
  simpa only [heatDuhamel_slabSourceExtension ht] using h



theorem gaugeDuhamel_c1_difference_bound_on_slab
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u v : ℝ → V → ℝ}
    {eta B L C d T t : ℝ} (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (ht : t ∈ Icc 0 T)
    (hb : ∀ s ∈ Icc 0 t, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 t, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hu : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |u s x| ≤ eta)
    (hv : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |v s x| ≤ eta)
    (hdu : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (u s) x‖ ≤ eta)
    (hdv : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (v s) x‖ ≤ eta)
    (huv : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |u s x - v s x| ≤ d)
    (hduv : ∀ s ∈ Icc 0 t, ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (u s) x - fderiv ℝ (v s) x‖ ≤ d)
    (hmu : StronglyMeasurable (fun p : Icc (0 : ℝ) T × V =>
      gaugeSource (b p.1) (G p.1) (u p.1) p.2))
    (hmv : StronglyMeasurable (fun p : Icc (0 : ℝ) T × V =>
      gaugeSource (b p.1) (G p.1) (v p.1) p.2))
    (hru : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (gaugeSource (b s) (G s) (u s)))
    (hrv : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (gaugeSource (b s) (G s) (v s)))
    (hbu : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (u s)) x‖ ≤ D)
    (hbv : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (v s)) x‖ ≤ D) (x : V) :
    (1 + ‖x‖) * ‖gaugeDuhamel b G u t x - gaugeDuhamel b G v t x‖ ≤
      (L + B + 2 * eta) * d * heatC1Gain (n + 1) t ∧
    (1 + ‖x‖) * ‖fderiv ℝ (gaugeDuhamel b G u t) x -
      fderiv ℝ (gaugeDuhamel b G v t) x‖ ≤
      (L + B + 2 * eta) * d * heatC1Gain (n + 1) t := by
  have hS : 0 ≤ B * eta + eta ^ 2 + L * eta + C := by positivity
  have hfu := gaugeSource_weighted_bound heta hB hL hb hGzero hGlip hu hdu
  have hfv := gaugeSource_weighted_bound heta hB hL hb hGzero hGlip hv hdv
  have hdiff (s : ℝ) (hs : s ∈ Icc 0 t) (y : V) :
      (1 + ‖y‖) * ‖gaugeSource (b s) (G s) (u s) y -
        gaugeSource (b s) (G s) (v s) y‖ ≤ (L + B + 2 * eta) * d := by
    have hua : |u s y| ≤ eta := by
      nlinarith [hu s hs y, mul_nonneg (norm_nonneg y) (abs_nonneg (u s y))]
    have hva : |v s y| ≤ eta := by
      nlinarith [hv s hs y, mul_nonneg (norm_nonneg y) (abs_nonneg (v s y))]
    have h := semilinearSource_weighted_lipschitz (by linarith [norm_nonneg y])
      (b s y) (G s y) (fderiv ℝ (u s) y) (fderiv ℝ (v s) y)
      (hb s hs y) (hdu s hs y) (hdv s hs y) (hGlip s hs y (u s y) (v s y) hua hva)
    have h1 := mul_le_mul_of_nonneg_left (huv s hs y) hL
    have h2 := mul_le_mul_of_nonneg_left (hduv s hs y) (show 0 ≤ B + 2 * eta by positivity)
    change (1 + ‖y‖) * |semilinearSource _ _ _ _ - semilinearSource _ _ _ _| ≤ _
    nlinarith [h, h1, h2]
  exact heatDuhamel_c1_difference_bound_on_slab hS hS (by positivity) ht
    hmu hmv hru hrv hbu hbv hfu hfv hdiff x



theorem gaugePicard_slab_geometric
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {eta B L C T : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hm : ∀ k, StronglyMeasurable (fun p : Icc (0 : ℝ) T × V =>
      gaugeSource (b p.1) (G p.1) (gaugePicard b G k p.1) p.2))
    (hr : ∀ k s, s ∈ Icc 0 T → ContDiff ℝ 1 (gaugeSource (b s) (G s) (gaugePicard b G k s)))
    (hbr : ∀ k s, s ∈ Ico 0 T → ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ D)
    (hball : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G k t x‖ ≤ eta ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta)
    (hcontract : (L + B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 2) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G (k + 1) t x - gaugePicard b G k t x‖ ≤
        eta * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G (k + 1) t) x -
        fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta * (1 / 2 : ℝ) ^ k := by
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
    have h := gaugeDuhamel_c1_difference_bound_on_slab heta hB hL hC hd ht
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
