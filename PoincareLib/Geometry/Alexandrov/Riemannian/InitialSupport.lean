import PoincareLib.Geometry.Riemannian.Comparison.Toponogov.Support.Initial
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Initial derivatives of hyperbolic distance supports

A squared-distance support selected along a prescribed minimizing segment
gives a cosh-distance support with the corresponding first-variation
derivative. This step does not require a curvature bound.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- A cosh-distance upper support whose first derivative retains the endpoint
velocity of the chosen minimizing segment. -/
theorem exists_cosh_distance_endpoint_support
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ σ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ σ 0) (hσ0 : σ 0 = γ 1) :
    ∃ u : ℝ → ℝ, u 0 = Real.cosh (g.edist (γ 0) (σ 0)).toReal ∧
      (∀ᶠ s in 𝓝 0, Real.cosh (g.edist (γ 0) (σ s)).toReal ≤ u s) ∧
      HasDerivAt u
        (Real.sinh (g.edist (γ 0) (γ 1)).toReal / (g.edist (γ 0) (γ 1)).toReal *
          g.inner (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) 0 := by
  obtain ⟨v, htouch, hupper, hv⟩ :=
    g.exists_squared_distance_endpoint_support D hcomplete hγ hneq hmin hσ hσ0
  let d : ℝ := (g.edist (γ 0) (γ 1)).toReal
  have hd : 0 < d := by
    let := g.toMetricSpace
    exact dist_pos.mpr hneq
  have hv0 : v 0 = d ^ 2 := by simpa only [hσ0] using htouch
  have hsqrt : Real.sqrt (v 0) = d := by rw [hv0, Real.sqrt_sq hd.le]
  refine ⟨fun s => Real.cosh (Real.sqrt (v s)), ?_, ?_, ?_⟩
  · dsimp only
    rw [htouch, Real.sqrt_sq ENNReal.toReal_nonneg]
  · filter_upwards [hupper] with s hs
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.le_sqrt ENNReal.toReal_nonneg (le_trans (sq_nonneg _) hs)).mpr hs
  · have hs := hv.sqrt (by rw [hv0]; exact pow_ne_zero 2 (ne_of_gt hd))
    have hc := hs.cosh
    rw [hsqrt] at hc
    convert! hc using 1
    dsimp [d] at *
    field_simp

end PoincareMT.RiemannianMetric
