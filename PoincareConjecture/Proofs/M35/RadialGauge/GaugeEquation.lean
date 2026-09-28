import PoincareConjecture.Proofs.M35.RadialGauge.SmoothExistence
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem gaugeSource_slab_continuous
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T : ℝ}
    (hb : Continuous (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hG : Continuous (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hu : Continuous (fun p : Icc 0 T × V => u p.1.1 p.2))
    (hdu : Continuous (fun p : Icc 0 T × V => fderiv ℝ (u p.1.1) p.2)) :
    Continuous (fun p : Icc 0 T × V =>
      gaugeSource (b p.1.1) (G p.1.1) (u p.1.1) p.2) := by
  exact ((hdu.clm_apply hb).add (hdu.norm.pow 2)).add
    (hG.comp (continuous_id.prodMk hu))

private theorem slabSourceExtension_contDiff {f : ℝ → V → ℝ} {T : ℝ}
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (f s)) (s : ℝ) :
    ContDiff ℝ ∞ (slabSourceExtension T f s) := by
  by_cases hs : s ∈ Icc 0 T
  · rw [slabSourceExtension_of_mem hs]
    exact hf s hs
  · have heq : slabSourceExtension T f s = fun _ => 0 := by
      funext x
      simp only [slabSourceExtension, if_neg hs]
    rw [heq]
    exact contDiff_const

private theorem slabSourceExtension_jet_bound {f : ℝ → V → ℝ} {T C : ℝ}
    (j : ℕ) (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ j (f s) x‖ ≤ C)
    (s : ℝ) (x : V) :
    ‖iteratedFDeriv ℝ j (slabSourceExtension T f s) x‖ ≤ max C 0 := by
  by_cases hs : s ∈ Icc 0 T
  · rw [slabSourceExtension_of_mem hs]
    exact (hb s hs x).trans (le_max_left _ _)
  · have heq : slabSourceExtension T f s = fun _ => 0 := by
      funext y
      simp only [slabSourceExtension, if_neg hs]
    rw [heq, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact le_max_right _ _

theorem slab_mild_solution_solves_heat
    {f u : ℝ → V → ℝ} {T t : ℝ}
    (hf : Continuous (fun p : Icc 0 T × V => f p.1.1 p.2))
    (hs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (f s))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ C)
    (hmild : ∀ s ∈ Icc 0 T, ∀ x, u s x = heatDuhamel f s x)
    (ht : t ∈ Ioo 0 T) (x : V) :
    HasDerivAt (fun s => u s x) (euclideanLaplacian (u t) x + f t x) t := by
  let E := slabSourceExtension T f
  have hEm := slabSourceExtension_stronglyMeasurable hf.stronglyMeasurable
  have hEs := slabSourceExtension_contDiff hs
  choose C hC using hb
  have hEb (j : ℕ) (s : ℝ) (y : V) := slabSourceExtension_jet_bound j (hC j) s y
  have hloc : ∀ᶠ s in 𝓝 t, s ∈ Icc 0 T := Icc_mem_nhds ht.1 ht.2
  have htime : ContinuousAt (fun s => E s x) t := by
    have hft : ContinuousOn (fun s => f s x) (Icc 0 T) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (hf.comp (continuous_id.prodMk continuous_const))
    apply (hft.continuousAt hloc).congr_of_eventuallyEq
    filter_upwards [hloc] with s hs'
    exact congrFun (slabSourceExtension_of_mem hs' f) x
  have hPDE := heatDuhamel_solves_heat ht.1.le hEm
    (fun s => (hEs s).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun s y => by simpa only [norm_iteratedFDeriv_zero] using hEb 0 s y)
    (fun s y => by simpa only [norm_iteratedFDeriv_one] using hEb 1 s y)
    (fun s y => by
      simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
        using hEb 2 s y) x htime
  have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have heq : heatDuhamel E t = u t := by
    rw [heatDuhamel_slabSourceExtension htcc]
    exact funext (fun y => (hmild t htcc y).symm)
  change HasDerivAt (fun s => heatDuhamel E s x)
    (euclideanLaplacian (heatDuhamel E t) x + E t x) t at hPDE
  rw [heq, show E t x = f t x from congrFun (slabSourceExtension_of_mem htcc f) x] at hPDE
  apply hPDE.congr_of_eventuallyEq
  filter_upwards [hloc] with s hs'
  rw [heatDuhamel_slabSourceExtension hs']
  exact hmild s hs' x

theorem gauge_smooth_mild_solves_heat
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T t : ℝ}
    (hb : Continuous (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hG : Continuous (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hu : Continuous (fun p : Icc 0 T × V => u p.1.1 p.2))
    (hdu : Continuous (fun p : Icc 0 T × V => fderiv ℝ (u p.1.1) p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hus : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (u s))
    (hsource : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (gaugeSource (b s) (G s) (u s)) x‖ ≤ C)
    (hmild : ∀ s ∈ Icc 0 T, ∀ x, u s x = gaugeDuhamel b G u s x)
    (ht : t ∈ Ioo 0 T) (x : V) :
    HasDerivAt (fun s => u s x)
      (euclideanLaplacian (u t) x + gaugeSource (b t) (G t) (u t) x) t := by
  exact slab_mild_solution_solves_heat (gaugeSource_slab_continuous hb hG hu hdu)
    (fun s hs => gaugeSource_contDiff (hbs s hs) (hGs s hs) (hus s hs))
    hsource hmild ht x

end PoincareConjecture.M35.RadialGauge
