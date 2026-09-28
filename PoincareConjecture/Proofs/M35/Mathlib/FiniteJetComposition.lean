import Mathlib.Analysis.Calculus.ContDiff.Comp









set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35



theorem tendsto_iteratedFDeriv_comp_of_jets
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℕ → E → F} {g : ℕ → F → G} {f₀ : E → F} {g₀ : F → G}
    {p : ℕ → E} {p₀ : E} (r : ℕ)
    (hf₀ : ContDiffAt ℝ ∞ f₀ p₀) (hg₀ : ContDiffAt ℝ ∞ g₀ (f₀ p₀))
    (hf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hg : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (g k) (f k (p k)))
    (hfjet : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ m f₀ p₀)))
    (hgjet : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (g k) (f k (p k))) atTop
      (𝓝 (iteratedFDeriv ℝ m g₀ (f₀ p₀)))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (g k ∘ f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (g₀ ∘ f₀) p₀)) := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  rw [iteratedFDeriv_comp hg₀ hf₀ hr]
  have hseries : Tendsto (fun k =>
      (ftaylorSeries ℝ (g k) (f k (p k))).taylorComp (ftaylorSeries ℝ (f k) (p k)) r)
      atTop (𝓝 ((ftaylorSeries ℝ g₀ (f₀ p₀)).taylorComp (ftaylorSeries ℝ f₀ p₀) r)) := by
    unfold FormalMultilinearSeries.taylorComp
    apply tendsto_finsetSum
    intro c _
    let B := c.compAlongOrderedFinpartitionL ℝ E F G
    exact (B.continuous_uncurry_of_multilinear.tendsto _).comp
      ((hgjet c.length c.length_le).prodMk_nhds
        (tendsto_pi_nhds.mpr (fun i => hfjet (c.partSize i) (c.partSize_le i))))
  apply hseries.congr'
  filter_upwards [hf, hg] with k hfk hgk
  exact (iteratedFDeriv_comp hgk hfk hr).symm

end PoincareConjecture.M35
