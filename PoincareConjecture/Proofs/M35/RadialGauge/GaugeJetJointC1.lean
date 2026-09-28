import PoincareConjecture.Proofs.M35.RadialGauge.GaugeTimeJets
import PoincareConjecture.Proofs.M35.RadialGauge.JetJointC1

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem gauge_smooth_mild_jets_joint_c1
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
    (hmild : ∀ s ∈ Icc 0 T, ∀ x, u s x = gaugeDuhamel b G u s x) (j : ℕ) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => iteratedFDeriv ℝ j (u p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  have htime := gauge_smooth_mild_spatial_time_jets hb hG hu hdu hbs hGs hus hub hsource hmild
  have hub' : ∀ k : ℕ, ∃ C : ℝ, ∀ s : Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ k (u s.1) x‖ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := hub k
    exact ⟨C, fun s => hC s.1 s.2⟩
  obtain ⟨hls, hlc, hlb⟩ := euclideanLaplacian_family_controls
    (u := fun s : Icc 0 T => u s.1) hu (fun s : Icc 0 T => hus s.1 s.2) hub'
  have hss (s : ℝ) (hs : s ∈ Icc 0 T) :=
    gaugeSource_contDiff (hbs s hs) (hGs s hs) (hus s hs)
  let H (s : ℝ) (x : V) := euclideanLaplacian (u s) x + gaugeSource (b s) (G s) (u s) x
  have hHc : Continuous (fun p : Icc 0 T × V => H p.1.1 p.2) :=
    hlc.add (gaugeSource_slab_continuous hb hG hu hdu)
  have hHs (s : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (H s.1) := (hls s).add (hss s.1 s.2)
  have hHb : ∀ k : ℕ, ∃ C : ℝ, ∀ s : Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ k (H s.1) x‖ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := hlb k
    obtain ⟨D, hD⟩ := hsource k
    refine ⟨C + D, fun s x => ?_⟩
    change ‖iteratedFDeriv ℝ k (fun y => euclideanLaplacian (u s.1) y +
      gaugeSource (b s.1) (G s.1) (u s.1) y) x‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply
      ((hls s).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt
      ((hss s.1 s.2).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hC s x) (hD s.1 s.2 x))
  have hHj (k : ℕ) := spatial_jets_jointly_continuous_of_uniform_bounds
    (f := fun s : Icc 0 T => H s.1) hHc hHs hHb k
  exact spatial_jets_joint_c1_of_time_equation hus htime.1 hHj htime.2 j

end PoincareConjecture.M35.RadialGauge
