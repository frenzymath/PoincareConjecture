import PoincareConjecture.Proofs.M35.RadialGauge.GaugeTimeJets
import PoincareConjecture.Proofs.M35.RadialGauge.JointC1











set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem gauge_smooth_mild_joint_c1
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T : ℝ}
    (hb : Continuous (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hG : Continuous (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hu : Continuous (fun p : Icc 0 T × V => u p.1.1 p.2))
    (hdu : Continuous (fun p : Icc 0 T × V => fderiv ℝ (u p.1.1) p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hus : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (u s))
    (hub : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (u s) x‖ ≤ C)
    (hsource : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (gaugeSource (b s) (G s) (u s)) x‖ ≤ C)
    (hmild : ∀ s ∈ Icc 0 T, ∀ x, u s x = gaugeDuhamel b G u s x) :
    ContDiffOn ℝ 1 (Function.uncurry u) (Ioo 0 T ×ˢ univ) := by
  have hub' : ∀ j : ℕ, ∃ C : ℝ, ∀ s : Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ j (u s.1) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hub j
    exact ⟨C, fun s => hC s.1 s.2⟩
  have hlc := (euclideanLaplacian_family_controls
    (u := fun s : Icc 0 T => u s.1) hu (fun s : Icc 0 T => hus s.1 s.2) hub').2.1
  have hsc := gaugeSource_slab_continuous hb hG hu hdu
  exact joint_contDiffOn_one_of_slab_partials
    (fun s hs => (hus s hs).differentiable (by simp))
    (fun s hs x => gauge_smooth_mild_solves_heat hb hG hu hdu
      hbs hGs hus hsource hmild hs x) (hlc.add hsc) hdu

end PoincareConjecture.M35.RadialGauge
