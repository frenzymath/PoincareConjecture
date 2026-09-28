import PoincareConjecture.Proofs.M35.RadialGauge.MildExistence
import PoincareConjecture.Proofs.M35.RadialGauge.PicardSmoothBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))




theorem exists_gauge_smooth_mild_solution
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B L C : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ k : ℕ, ∃ D : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ k (b s) x‖ ≤ D)
    (hGb : ∀ k : ℕ, ∃ D : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ D)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hsmall : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) T ≤ eta)
    (hcontract : (L + B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 2)
    (hhigh : (B + 2 * (n + 1 : ℕ) * eta) *
      (2 * gaussianFirstMoment (n + 1) * Real.sqrt T) ≤ 1 / 2) :
    ∃ u : ℝ → V → ℝ,
      StronglyMeasurable (fun p : Icc 0 T × V => u p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => u p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (u p.1.1) p.2) ∧
      u 0 = 0 ∧ (∀ t, t ∉ Icc 0 T → u t = 0) ∧
      (∀ j : ℕ, ∃ D : ℝ, ∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ j (u t) x‖ ≤ D) ∧
      (∀ j : ℕ, ∃ D : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (gaugeSource (b t) (G t) (u t)) x‖ ≤ D) ∧
      ∀ t, t ∈ Icc 0 T → ContDiff ℝ ∞ (u t) ∧
        (∀ x, u t x = gaugeDuhamel b G u t x) ∧
        (∀ x, (1 + ‖x‖) * ‖u t x‖ ≤ eta ∧
          (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ ≤ eta) ∧
        TendstoUniformly (fun k => gaugePicard b G k t) (u t) atTop ∧
        TendstoUniformly (fun k => fderiv ℝ (gaugePicard b G k t)) (fderiv ℝ (u t)) atTop ∧
        ∀ k x, (1 + ‖x‖) * ‖gaugePicard b G k t x - u t x‖ ≤
            2 * eta * (1 / 2 : ℝ) ^ k ∧
          (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x - fderiv ℝ (u t) x‖ ≤
            2 * eta * (1 / 2 : ℝ) ^ k := by
  have hc := gaugePicard_slab_control hT heta hB hL hC hbm hGm hbs hGs hbb hGb
    hb hGzero hGlip hsmall
  have hpb := gaugePicard_uniform_all_order_bounds hT heta hB hc hbm hGm hbs hGs
    hbb hGb hb hhigh
  choose D hDnonneg hD using hpb
  obtain ⟨u, hmu, hcu, hcdu, hu0, hout, hu⟩ := exists_gauge_mild_solution
    hT heta hB hL hC hbm hGm hbs hGs hbb hGb hb hGzero hGlip hsmall hcontract
  have hlimit (t : ℝ) (ht : t ∈ Icc 0 T) := contDiff_limit_and_uniform_jet_bounds
    (fun k => (hc k).smooth t ht) (fun j k x => hD j k t ht x)
    (fun x => (hu t ht).2.2.2.1.tendsto_at x)
  have hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (u t) := fun t ht => (hlimit t ht).1
  have hub : ∀ j : ℕ, ∃ D : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (u t) x‖ ≤ D :=
    fun j => ⟨D j, fun t ht x => (hlimit t ht).2 j x⟩
  have huv (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) : |u t x| ≤ eta := by
    have h := (hu t ht).2.2.1 x |>.1
    rw [Real.norm_eq_abs] at h
    nlinarith only [h, mul_nonneg (norm_nonneg x) (abs_nonneg (u t x))]
  let : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  have hsource := gaugeSource_uniform_bounded_derivatives
    (b := fun t : Icc 0 T => b t.1) (G := fun t : Icc 0 T => G t.1)
    (u := fun t : Icc 0 T => u t.1)
    (fun t => hbs t.1 t.2) (fun t => hGs t.1 t.2) (fun t => hs t.1 t.2)
    (fun t => huv t.1 t.2)
    (fun j => by
      obtain ⟨D, hD⟩ := hbb j
      exact ⟨D, fun t => hD t.1 t.2⟩)
    (fun j => by
      obtain ⟨D, hD⟩ := hub j
      exact ⟨D, fun t => hD t.1 t.2⟩)
    (fun j => by
      obtain ⟨D, hD⟩ := hGb j
      exact ⟨D, fun t => hD t.1 t.2⟩)
  refine ⟨u, hmu, hcu, hcdu, hu0, hout, hub, ?_, fun t ht => ⟨hs t ht, (hu t ht).2⟩⟩
  intro j
  obtain ⟨E, hE⟩ := hsource j
  exact ⟨E, fun t ht => hE ⟨t, ht⟩⟩

end PoincareConjecture.M35.RadialGauge
