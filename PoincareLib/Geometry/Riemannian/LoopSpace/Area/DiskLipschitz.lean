import PoincareLib.Geometry.Riemannian.LoopSpace.Area.DerivativeBounds
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Path
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# C1 disk maps are Lipschitz on the disk

This verifies the metric Lipschitz requirement in Morgan--Tian
Definition 18.17, printed p. 430, for the disk construction of Corollary 18.28,
p. 434. The argument integrates the metric derivative along straight source
segments. The constant depends on the map, as allowed by the contract.
See the task's disk-extension derivation.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.LoopSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- A metric derivative bound on the convex disk controls the distance
between image points. Source: MT Definition 18.17, p. 430, disk-extension derivation. -/
theorem disk_edist_le_of_derivative_bound (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) {K : ℝ}
    (hD : ∀ z ∈ loopDiskSet, ∀ v : LoopPlane,
      g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 3) F z v) ≤ K * ‖v‖)
    {x y : LoopPlane} (hx : x ∈ loopDiskSet) (hy : y ∈ loopDiskSet) :
    g.edist (F x) (F y) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let δ : ℝ → LoopPlane := AffineMap.lineMap x y
  have hδ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 δ := (AffineMap.contDiff_lineMap x y).contMDiff
  have hpath : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (F ∘ δ) := hF.comp hδ
  have hδvelocity (t : ℝ) : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) δ t 1 = y - x := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).deriv
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1, pathSpeed g (F ∘ δ) t ≤ K * ‖y - x‖ := by
    intro t ht
    have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (F ∘ δ) t 1 =
        mfderiv (𝓡 2) (𝓡 3) F (δ t) (y - x) := by
      rw [mfderiv_comp_apply t (hF.mdifferentiableAt one_ne_zero)
        (hδ.mdifferentiableAt one_ne_zero), hδvelocity]
    dsimp only [pathSpeed]
    rw [hvelocity]
    exact hD (δ t) ((convex_closedBall (0 : LoopPlane) 1).lineMap_mem hx hy ht) (y - x)
  have hdist : g.edist (F x) (F y) ≤ g.pathELength (F ∘ δ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpath.contMDiffOn
      (by simp [δ]) (by simp [δ]) zero_le_one
  rw [pathELength_eq_ofReal_integral_pathSpeed g hpath zero_le_one] at hdist
  have hint : (∫ t in (0 : ℝ)..1, pathSpeed g (F ∘ δ) t) ≤ K * ‖y - x‖ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      ((continuous_pathSpeed g hpath).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) hspeed
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h
  calc
    g.edist (F x) (F y) ≤ ENNReal.ofReal (K * ‖y - x‖) :=
      hdist.trans (ENNReal.ofReal_le_ofReal hint)
    _ = ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := by
      rw [ENNReal.ofReal_mul' (norm_nonneg _), norm_sub_rev]

/-- A global C1 map into the supplied Riemannian manifold is Lipschitz
on the compact unit disk. Source: MT Corollary 18.28, printed p. 434. -/
theorem exists_disk_lipschitz_constant (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : LoopDisk,
      g.edist (F x.val) (F y.val) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖x.val - y.val‖ := by
  obtain ⟨K, hK, hD⟩ := exists_disk_derivative_bound g hF
  exact ⟨K, hK, fun x y => disk_edist_le_of_derivative_bound g hF hD x.property y.property⟩

end PoincareMT.LoopSpace
