import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Rigidity
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_ancient_reducedVolume_limit
    (F : RicciFlow n M (Iic 0))
    (hV : ∀ R : ℝ, 0 < R → Nonempty (ReducedVolumeTheory F 0 R)) (p : M) :
    ∃ V : ℝ, 0 ≤ V ∧
      (∀ τ : ℝ, 0 < τ → V ≤ reducedVolume F 0 p τ) ∧
      Tendsto (reducedVolume F 0 p) atTop (𝓝 V) ∧
      ∀ a : ℕ → ℝ, Tendsto a atTop atTop → ∀ τ : ℝ, 0 < τ →
        Tendsto (fun k ↦ reducedVolume F 0 p (a k * τ)) atTop (𝓝 V) := by
  have hpos (τ : ℝ) (hτ : 0 < τ) : 0 < reducedVolume F 0 p τ := by
    obtain ⟨Q⟩ := hV (τ + 1) (by linarith)
    exact (Q.volume_bounds p τ hτ (by linarith)).1
  have hmono : AntitoneOn (reducedVolume F 0 p) (Ioi 0) := by
    intro a ha b hb hab
    change 0 < a at ha
    change 0 < b at hb
    obtain ⟨Q⟩ := hV (b + 1) (by linarith)
    exact Q.monotone p ⟨ha, by linarith⟩ ⟨hb, by linarith⟩ hab
  let f : ℝ → ℝ := fun t ↦ reducedVolume F 0 p (max t 1)
  have hf : Antitone f := by
    intro s t hst
    exact hmono (by change 0 < max s 1; positivity)
      (by change 0 < max t 1; positivity) (max_le_max_right 1 hst)
  have hnonneg (t : ℝ) : 0 ≤ f t :=
    (hpos _ (lt_of_lt_of_le zero_lt_one (le_max_right t 1))).le
  have hbdd : BddBelow (range f) := ⟨0, by rintro _ ⟨t, rfl⟩; exact hnonneg t⟩
  have hlim : Tendsto (reducedVolume F 0 p) atTop (𝓝 (⨅ t, f t)) := by
    apply (tendsto_atTop_ciInf hf hbdd).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simp only [f, max_eq_left ht]
  refine ⟨⨅ t, f t, le_ciInf hnonneg, ?_, hlim, ?_⟩
  · intro τ hτ
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop τ] with t ht
    exact hmono hτ (lt_of_lt_of_le hτ ht) ht
  · intro a ha τ hτ
    exact hlim.comp (ha.atTop_mul_const hτ)

theorem exists_ancient_reducedVolume_limit_lt_euclidean
    (F : RicciFlow n M (Iic 0))
    (hV : ∀ R : ℝ, 0 < R → Nonempty (ReducedVolumeTheory F 0 R)) (p x : M)
    (hscalar : 0 < (F.connection (-1 / 2)).scalarCurvature x) :
    ∃ V : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧
      Tendsto (reducedVolume F 0 p) atTop (𝓝 V) ∧
      ∀ a : ℕ → ℝ, Tendsto a atTop atTop → ∀ τ : ℝ, 0 < τ →
        Tendsto (fun k ↦ reducedVolume F 0 p (a k * τ)) atTop (𝓝 V) := by
  obtain ⟨V, hV0, hVle, hlim, hdilate⟩ := exists_ancient_reducedVolume_limit F hV p
  obtain ⟨Q⟩ := hV 2 (by norm_num)
  refine ⟨V, hV0, ?_, hlim, hdilate⟩
  exact lt_of_le_of_lt (hVle 1 zero_lt_one)
    (reducedVolume_lt_euclidean_of_scalar_pos Q zero_lt_one (by norm_num) p x hscalar)

end PoincareConjecture
