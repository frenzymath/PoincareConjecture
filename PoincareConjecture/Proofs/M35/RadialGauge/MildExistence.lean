import PoincareConjecture.Proofs.M35.RadialGauge.PicardRegularity
import PoincareConjecture.Proofs.M35.RadialGauge.SlabContraction
import PoincareConjecture.Proofs.M35.RadialGauge.PicardMildEquation
import PoincareConjecture.Proofs.M35.RadialGauge.PicardContinuity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))




theorem exists_gauge_mild_solution
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
    (hcontract : (L + B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 2) :
    ∃ u : ℝ → V → ℝ,
      StronglyMeasurable (fun p : Icc 0 T × V => u p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => u p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (u p.1.1) p.2) ∧
      u 0 = 0 ∧ (∀ t, t ∉ Icc 0 T → u t = 0) ∧
      ∀ t, t ∈ Icc 0 T → ContDiff ℝ 1 (u t) ∧
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
  have hs (k : ℕ) := (hc k).source hT hbm hGm hbs hGs hbb hGb
  have hr (k : ℕ) (s : ℝ) (hs' : s ∈ Icc 0 T) :
      ContDiff ℝ 1 (gaugeSource (b s) (G s) (gaugePicard b G k s)) :=
    ((hs k).2.1 s hs').of_le (by simp)
  have hbr (k : ℕ) (s : ℝ) (hs' : s ∈ Ico 0 T) :
      ∃ D : ℝ, ∀ x, ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ D := by
    obtain ⟨D, hD⟩ := (hs k).2.2 1
    exact ⟨D, fun x => by simpa only [norm_iteratedFDeriv_one] using hD s ⟨hs'.1, hs'.2.le⟩ x⟩
  have hball := fun k => (hc k).weighted
  have hstep := gaugePicard_slab_geometric heta hB hL hC hb hGzero hGlip
    (fun k => (hs k).1) hr hbr hball hcontract
  obtain ⟨u, hout, hu⟩ := exists_gaugePicard_c1_limit hball hstep
    (fun k t ht => ((hc k).smooth t ht).differentiable (by simp))
  have hv := fun t ht x => (hu t ht).2.1.tendsto_at x
  have hd := fun t ht x => (hu t ht).2.2.1.tendsto_at x
  have hmild := gaugePicard_limit_mild_equation heta hB hL hb hGzero hGlip
    (fun k => (hs k).1) (fun k t ht => (hr k t ht).continuous) hball hv hd
  have hm : StronglyMeasurable (fun p : Icc 0 T × V => u p.1.1 p.2) :=
    stronglyMeasurable_of_tendsto atTop (fun k => (hc k).measurable)
      (tendsto_pi_nhds.mpr (fun p => hv p.1.1 p.1.2 p.2))
  have hjoint := gaugePicard_limit_joint_continuous (gaugePicard_slab_continuous hs)
    (fun k t ht => (hu t ht).2.2.2.2 k)
  refine ⟨u, hm, hjoint.1, hjoint.2, ?_, hout, ?_⟩
  · funext x
    rw [hmild 0 ⟨le_rfl, hT⟩ x]
    simp only [gaugeDuhamel, intervalIntegral.integral_same, Pi.zero_apply]
  intro t ht
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨(hu t ht).1, ?_⟩,
    hmild t ht, (hu t ht).2.2.2.1, (hu t ht).2.1, (hu t ht).2.2.1, (hu t ht).2.2.2.2⟩
  exact (hu t ht).2.2.1.continuous (Eventually.of_forall (fun k =>
    (contDiff_infty_iff_fderiv.mp ((hc k).smooth t ht)).2.continuous)).frequently

end PoincareConjecture.M35.RadialGauge
