import PoincareConjecture.Proofs.M35.RadialGauge.RadiusInverseContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.SmoothEuclideanGauge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem radial_diffeomorph_symm_apply
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞) {w q : ℝ → ℝ}
    (hΦ : ∀ x, Φ x = Real.exp (w ‖x‖) • x)
    (hq : ∀ r, mapRadius w (q r) = r) (x : V) :
    Φ.symm x = Real.exp (-w (q ‖x‖)) • x := by
  let y := Real.exp (-w (q ‖x‖)) • x
  have he : Real.exp (-w (q ‖x‖)) * Real.exp (w (q ‖x‖)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hynorm : ‖y‖ = q ‖x‖ := by
    dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-w (q ‖x‖)) * ‖x‖ =
          Real.exp (-w (q ‖x‖)) * mapRadius w (q ‖x‖) :=
        congrArg (fun r => Real.exp (-w (q ‖x‖)) * r) (hq ‖x‖).symm
      _ = q ‖x‖ * (Real.exp (-w (q ‖x‖)) * Real.exp (w (q ‖x‖))) := by
        dsimp only [mapRadius]
        ring
      _ = q ‖x‖ := by rw [he, mul_one]
  apply Φ.injective
  change Φ (Φ.symm x) = Φ y
  rw [Φ.apply_symm_apply, hΦ, hynorm]
  change x = Real.exp (w (q ‖x‖)) • (Real.exp (-w (q ‖x‖)) • x)
  rw [smul_smul, mul_comm, he, one_smul]

theorem radial_diffeomorph_symm_continuousOn
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {w : ℝ → ℝ → ℝ} {J : Set ℝ}
    (hΦ : ∀ t ∈ J, ∀ x, Φ t x = Real.exp (w t ‖x‖) • x)
    (hc : ContinuousOn (Function.uncurry w) (J ×ˢ univ))
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (w t))
    (hv : ∀ t ∈ J, ∀ r, (1 + |r|) * |w t r| ≤ 1 / 8)
    (hd : ∀ t ∈ J, ∀ r, (1 + |r|) * |deriv (w t) r| ≤ 1 / 8) :
    ContinuousOn (fun p : ℝ × V => (Φ p.1).symm p.2) (J ×ˢ univ) := by
  have hq : ContinuousOn
      (fun p : ℝ × V => mapRadiusInverse w p.1 ‖p.2‖) (J ×ˢ univ) :=
    (mapRadiusInverse_continuousOn hc hs hv hd).comp
      (f := fun p : ℝ × V => (p.1, ‖p.2‖))
      (continuousOn_fst.prodMk continuousOn_snd.norm)
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hw : ContinuousOn
      (fun p : ℝ × V => w p.1 (mapRadiusInverse w p.1 ‖p.2‖)) (J ×ˢ univ) :=
    hc.comp (f := fun p : ℝ × V => (p.1, mapRadiusInverse w p.1 ‖p.2‖))
      (continuousOn_fst.prodMk hq) (fun _ hp => ⟨hp.1, mem_univ _⟩)
  apply (hw.neg.rexp.smul continuousOn_snd).congr
  intro p hp
  exact radial_diffeomorph_symm_apply (Φ p.1) (hΦ p.1 hp.1)
    (mapRadius_inverse_properties (hs p.1 hp.1) (hv p.1 hp.1) (hd p.1 hp.1)).2.2.1 p.2

end PoincareConjecture.M35.RadialGauge
