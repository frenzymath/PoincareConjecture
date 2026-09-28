import PoincareConjecture.Proofs.M35.RadialGauge.GaugeEquation
import PoincareConjecture.Proofs.M35.RadialGauge.LaplacianFamily
import PoincareConjecture.Proofs.M35.RadialGauge.TimeSpatialJets

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem gauge_smooth_mild_spatial_time_jets
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
    (∀ j : ℕ, Continuous
      (fun p : Icc 0 T × V => iteratedFDeriv ℝ j (u p.1.1) p.2)) ∧
    ∀ (j : ℕ) (t : ℝ), t ∈ Ioo 0 T → ∀ x,
      HasDerivAt (fun s => iteratedFDeriv ℝ j (u s) x)
        (iteratedFDeriv ℝ j (fun y => euclideanLaplacian (u t) y +
          gaugeSource (b t) (G t) (u t) y) x) t := by
  have hub' : ∀ j : ℕ, ∃ C : ℝ, ∀ s : Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ j (u s.1) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hub j
    exact ⟨C, fun s => hC s.1 s.2⟩
  have huc (j : ℕ) := spatial_jets_jointly_continuous_of_uniform_bounds
    (f := fun s : Icc 0 T => u s.1) hu (fun s : Icc 0 T => hus s.1 s.2) hub' j
  obtain ⟨hls, hlc, hlb⟩ := euclideanLaplacian_family_controls
    (u := fun s : Icc 0 T => u s.1) hu (fun s : Icc 0 T => hus s.1 s.2) hub'
  have hsc := gaugeSource_slab_continuous hb hG hu hdu
  have hss (s : ℝ) (hs : s ∈ Icc 0 T) :=
    gaugeSource_contDiff (hbs s hs) (hGs s hs) (hus s hs)
  let H (s : ℝ) (x : V) := euclideanLaplacian (u s) x +
    gaugeSource (b s) (G s) (u s) x
  have hHc : Continuous (fun p : Icc 0 T × V => H p.1.1 p.2) := hlc.add hsc
  have hHs (s : ℝ) (hs : s ∈ Icc 0 T) : ContDiff ℝ ∞ (H s) :=
    (hls ⟨s, hs⟩).add (hss s hs)
  have hHb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (H s) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hlb j
    obtain ⟨D, hD⟩ := hsource j
    refine ⟨C + D, fun s hs x => ?_⟩
    rw [show H s = fun y => euclideanLaplacian (u s) y +
      gaugeSource (b s) (G s) (u s) y from rfl]
    rw [fun_iteratedFDeriv_add_apply
      ((hls ⟨s, hs⟩).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt
      ((hss s hs).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hC ⟨s, hs⟩ x) (hD s hs x))
  refine ⟨huc, fun j t ht x => ?_⟩
  have hsub : Ioo (0 : ℝ) T ⊆ Icc 0 T := Ioo_subset_Icc_self
  apply time_spatial_jets_interchange j
    (fun s hs => hus s (hsub hs)) (fun s hs => hHs s (hsub hs))
    (hHc.comp (f := fun p : Ioo 0 T × V =>
      ((⟨p.1.1, hsub p.1.2⟩ : Icc 0 T), p.2)) (by fun_prop))
    (fun k => by
      obtain ⟨C, hC⟩ := hHb k
      exact ⟨C, fun s hs => hC s (hsub hs)⟩)
    (fun s hs y => gauge_smooth_mild_solves_heat hb hG hu hdu
      hbs hGs hus hsource hmild hs y) ht x

end PoincareConjecture.M35.RadialGauge
