import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.MovingEndpoints.Increment
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem eventually_moving_distance_slope_lt
    (F : RicciFlow n M J) {γ η : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ η I)
    {t : ℝ} (hflow : -t ∈ interior J) (ht : t ∈ I)
    {u : ℝ → ℝ} {d r : ℝ}
    (hu : u t = ((F.metric (-t)).edist (γ t) (η t)).toReal)
    (hupper : ∀ s, ((F.metric (-s)).edist (γ t) (η t)).toReal ≤ u s)
    (hd : HasDerivAt u d t)
    (hr : d + (F.metric (-t)).tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) +
      (F.metric (-t)).tangentNorm (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1) < r) :
    ∀ᶠ s in 𝓝[>] t,
      slope (fun s => ((F.metric (-s)).edist (γ s) (η s)).toReal) t s < r := by
  let a := (F.metric (-t)).tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
  let b := (F.metric (-t)).tangentNorm (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1)
  let ε := (r - (d + a + b)) / 4
  have hε : 0 < ε := by dsimp [ε, a, b]; linarith
  obtain ⟨δγ, hδγ, hincγ⟩ := F.exists_right_endpoint_distance_increment_bound hI hγ hflow ht hε
  obtain ⟨δη, hδη, hincη⟩ := F.exists_right_endpoint_distance_increment_bound hI hη hflow ht hε
  have hslope : ∀ᶠ s in 𝓝[>] t, slope u t s < d + ε := by
    have hle : 𝓝[>] t ≤ 𝓝[≠] t := nhdsWithin_mono t (fun s hs => by
      simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt hs)
    exact (hd.tendsto_slope.mono_left hle).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hslope, Ioo_mem_nhdsGT (show t < t + δγ by linarith),
    Ioo_mem_nhdsGT (show t < t + δη by linarith)] with s hsu hsγ hsη
  have hs : 0 < s - t := sub_pos.mpr hsγ.1
  have hγdist := hincγ s ⟨hsγ.1.le, hsγ.2.le⟩
  have hηdist := hincη s ⟨hsη.1.le, hsη.2.le⟩
  have htri : ((F.metric (-s)).edist (γ s) (η s)).toReal ≤
      ((F.metric (-s)).edist (γ t) (γ s)).toReal + u s +
        ((F.metric (-s)).edist (η t) (η s)).toReal := by
    let := (F.metric (-s)).toMetricSpace
    change dist (γ s) (η s) ≤ dist (γ t) (γ s) + u s + dist (η t) (η s)
    have h₁ := dist_triangle (γ s) (γ t) (η s)
    have h₂ := dist_triangle (γ t) (η t) (η s)
    have h₃ := hupper s
    change dist (γ t) (η t) ≤ u s at h₃
    rw [dist_comm (γ s) (γ t)] at h₁
    linarith
  rw [slope_def_field, ← hu]
  apply (div_lt_iff₀ hs).mpr
  rw [slope_def_field] at hsu
  have hsu' := (div_lt_iff₀ hs).mp hsu
  change _ ≤ (a + ε) * (s - t) at hγdist
  change _ ≤ (b + ε) * (s - t) at hηdist
  have hgap : d + a + b + 3 * ε < r := by dsimp [ε]; linarith
  have hgap' := mul_lt_mul_of_pos_right hgap hs
  nlinarith

end PoincareConjecture.RicciFlow
