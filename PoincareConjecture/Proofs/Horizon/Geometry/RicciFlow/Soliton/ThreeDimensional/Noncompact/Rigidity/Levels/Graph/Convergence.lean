import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Local








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]



theorem exists_level_graphs_tendsto_C1
    (F : ℕ → ℝ × N → ℝ) (V : ℕ → Set (ℝ × N)) (hV : ∀ k, IsOpen (V k))
    {ε : ℝ} (hε : 0 < ε) (ν : N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsmooth : ∀ᶠ k in atTop,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ (F k) (V k) ∧
        Icc (-ε) ε ×ˢ (univ : Set N) ⊆ V k)
    (hvalue : ∀ δ > 0, ∀ᶠ k in atTop, ∀ y : N, ∀ s ∈ Icc (-ε) ε,
      |F k (s, y) - s| ≤ δ)
    (hvertical : ∀ δ > 0, ∀ᶠ k in atTop, ∀ y : N, ∀ s ∈ Ioo (-ε) ε,
      |deriv (fun r => F k (r, y)) s - 1| ≤ δ)
    (hhorizontal : ∀ δ > 0, ∀ᶠ k in atTop, ∀ y : N, ∀ s ∈ Ioo (-ε) ε,
      ∀ v : EuclideanSpace ℝ (Fin n),
        |mvfderiv (𝓡 n) (fun z => F k (s, z)) y v| ≤ δ * ν y v) :
    ∃ u : ℕ → N → ℝ,
      (∀ᶠ k in atTop, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (u k) ∧
        (∀ y, u k y ∈ Ioo (-ε) ε ∧ F k (u k y, y) = 0) ∧
        ∀ y s, s ∈ Ioo (-ε) ε → (F k (s, y) = 0 ↔ s = u k y)) ∧
      ∀ δ > 0, ∀ᶠ k in atTop,
        (∀ y, |u k y| ≤ δ) ∧
        ∀ (y : N) (v : EuclideanSpace ℝ (Fin n)),
          |mvfderiv (𝓡 n) (u k) y v| ≤ δ * ν y v := by
  classical
  let good (k : ℕ) : Prop :=
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ (F k) (V k) ∧
      Icc (-ε) ε ×ˢ (univ : Set N) ⊆ V k ∧
      (∀ y : N, ∀ s ∈ Icc (-ε) ε, |F k (s, y) - s| ≤ ε / 2) ∧
      (∀ y : N, ∀ s ∈ Ioo (-ε) ε, (1 / 2 : ℝ) ≤ deriv (fun r => F k (r, y)) s) ∧
      ∀ y : N, ∀ s ∈ Ioo (-ε) ε, ∀ v : EuclideanSpace ℝ (Fin n),
        |mvfderiv (𝓡 n) (fun z => F k (s, z)) y v| ≤ 1 * ν y v
  have hg : ∀ᶠ k in atTop, good k := by
    filter_upwards [hsmooth, hvalue (ε / 2) (by positivity),
      hvertical (1 / 2) (by norm_num), hhorizontal 1 (by norm_num)] with k hk hv hd hh
    refine ⟨hk.1, hk.2, hv, ?_, hh⟩
    intro y s hs
    have h := (abs_le.mp (hd y s hs)).1
    linarith
  let P (k : ℕ) (u : N → ℝ) : Prop :=
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ y, u y ∈ Ioo (-ε) ε ∧ F k (u y, y) = 0) ∧
      ∀ y s, s ∈ Ioo (-ε) ε → (F k (s, y) = 0 ↔ s = u y)
  have hex (k : ℕ) : ∃ u : N → ℝ, good k → P k u := by
    by_cases hk : good k
    · obtain ⟨u, hu, hr, he, _, _⟩ := exists_level_height_with_C1_bounds_on
        (hV k) hk.1 hε (by linarith : ε / 2 < ε) hk.2.1 ν
        hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
      exact ⟨u, fun _ => ⟨hu, hr, he⟩⟩
    · exact ⟨fun _ => 0, fun h => (hk h).elim⟩
  choose u hu using hex
  refine ⟨u, hg.mono (fun k hk => hu k hk), ?_⟩
  intro δ hδ
  let r := min δ (ε / 2)
  have hr : 0 < r := lt_min hδ (by positivity)
  filter_upwards [hg, hvalue r hr, hhorizontal (δ / 2) (by positivity)] with k hk hv hh
  obtain ⟨w, _, hw, _, hheight, hdiff⟩ := exists_level_height_with_C1_bounds_on
    (hV k) hk.1 hε ((min_le_right δ (ε / 2)).trans_lt (by linarith)) hk.2.1 ν
    hv hk.2.2.2.1 hh
  have heq : u k = w := by
    funext y
    exact (((hu k hk).2.2 y (w y) (hw y).1).mp (hw y).2).symm
  rw [heq]
  refine ⟨fun y => (hheight y).trans (min_le_left _ _), ?_⟩
  intro y v
  simpa only [show 2 * (δ / 2) = δ by ring] using hdiff y v

end Poincare.Manifold
