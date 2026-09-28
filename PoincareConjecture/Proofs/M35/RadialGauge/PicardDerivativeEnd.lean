import PoincareConjecture.Proofs.M35.RadialGauge.PicardHessian
import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivativeEnd
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelJetEnd










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem gaugePicard_derivatives_weighted_vanish_uniformly
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B B1 L1 C1 H : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    (hL1 : 0 ≤ L1) (hC1 : 0 ≤ C1) (hH : 0 ≤ H)
    (hcontrol : ∀ k, PicardSlabControl T eta (gaugePicard b G k))
    (hHess : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤ H)
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (b s) x‖ ≤ C)
    (hGb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hdb : ∀ s ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (b s) x‖ ≤ B1)
    (hGx : ∀ s ∈ Icc 0 T, ∀ x z, (1 + ‖x‖) * |z| ≤ eta →
      (1 + ‖x‖) * ‖forcingSpaceDeriv (G s) x z‖ ≤ C1)
    (hGz : ∀ s ∈ Icc 0 T, ∀ x z, (1 + ‖x‖) * |z| ≤ eta →
      |forcingScalarDeriv (G s) x z| ≤ L1)
    (hGend : ∀ e > 0, ∃ R : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, R ≤ ‖x‖ →
      (1 + ‖x‖) * |z| ≤ eta → (1 + ‖x‖) * ‖forcingSpaceDeriv (G s) x z‖ < e) :
    ∀ k, ∀ e > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x‖ < e ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ < e := by
  intro k
  induction k with
  | zero =>
      intro e he
      refine ⟨0, fun t ht x hx => ?_⟩
      simpa only [gaugePicard, fderiv_fun_const, fderiv_zero, Pi.zero_apply,
        ContinuousLinearMap.opNorm_zero, mul_zero] using And.intro he he
  | succ k ih =>
      let C := (B + 2 * eta) * H + (B1 + L1) * eta + C1
      have hC : 0 ≤ C := by dsimp [C]; positivity
      obtain ⟨hsm, hss, hsb⟩ := (hcontrol k).source hT hbm hGm hbs hGs hbb hGb
      have hvalue (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) :
          (1 + ‖x‖) * |gaugePicard b G k t x| ≤ eta := by
        simpa only [Real.norm_eq_abs] using ((hcontrol k).weighted t ht x).1
      have hsourceBound (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) :
          (1 + ‖x‖) * ‖fderiv ℝ (gaugeSource (b t) (G t) (gaugePicard b G k t)) x‖ ≤ C := by
        have hu := (hcontrol k).smooth t ht
        exact gaugeSource_weighted_fderiv_bound heta hB hB1 hL1
          ((hbs t ht).differentiable (by simp) x) (hu.differentiable (by simp) x)
          ((contDiff_infty_iff_fderiv.mp hu).2.differentiable (by simp) x)
          ((hGs t ht).differentiable (by simp) (x, gaugePicard b G k t x))
          (hb t ht x) (hdb t ht x) ((hcontrol k).weighted t ht x).2 (hHess k t ht x)
          (hGx t ht x _ (hvalue t ht x)) (hGz t ht x _ (hvalue t ht x))
      have hsourceEnd := gaugeSource_weighted_fderiv_vanishes_uniformly
        (b := fun t : Icc 0 T => b t.1) (G := fun t : Icc 0 T => G t.1)
        (u := fun t : Icc 0 T => gaugePicard b G k t.1) heta hB hB1 hL1
        (fun t => hbs t.1 t.2) (fun t => hGs t.1 t.2)
        (fun t => (hcontrol k).smooth t.1 t.2)
        (fun t => hb t.1 t.2) (fun t => hdb t.1 t.2) (fun t => hGz t.1 t.2)
        (fun t => hvalue t.1 t.2) (fun t x => ((hcontrol k).weighted t.1 t.2 x).2)
        (fun e he => by
          obtain ⟨R, hR⟩ := ih e he
          exact ⟨R, fun t x hx => (hR t.1 t.2 x hx).1⟩)
        (fun e he => by
          obtain ⟨R, hR⟩ := ih e he
          exact ⟨R, fun t x hx => (hR t.1 t.2 x hx).2⟩)
        (fun e he => by
          obtain ⟨R, hR⟩ := hGend e he
          exact ⟨R, fun t => hR t.1 t.2⟩)
      exact heatDuhamel_derivatives_weighted_vanish_uniformly hC hT hsm hss hsb hsourceBound
        (fun e he => by
          obtain ⟨R, hR⟩ := hsourceEnd e he
          exact ⟨R, fun t ht => hR ⟨t, ht⟩⟩)

end PoincareConjecture.M35.RadialGauge
