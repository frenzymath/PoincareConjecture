import PoincareConjecture.Proofs.M58.Cor18_28_DerivativeBounds
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



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
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1, M04.pathSpeed g (F ∘ δ) t ≤ K * ‖y - x‖ := by
    intro t ht
    have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (F ∘ δ) t 1 =
        mfderiv (𝓡 2) (𝓡 3) F (δ t) (y - x) := by
      rw [mfderiv_comp_apply t (hF.mdifferentiableAt one_ne_zero)
        (hδ.mdifferentiableAt one_ne_zero), hδvelocity]
    dsimp only [M04.pathSpeed]
    rw [hvelocity]
    exact hD (δ t) ((convex_closedBall (0 : LoopPlane) 1).lineMap_mem hx hy ht) (y - x)
  have hdist : g.edist (F x) (F y) ≤ g.pathELength (F ∘ δ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpath.contMDiffOn
      (by simp [δ]) (by simp [δ]) zero_le_one
  rw [M04.pathELength_eq_ofReal_integral_pathSpeed g hpath zero_le_one] at hdist
  have hint : (∫ t in (0 : ℝ)..1, M04.pathSpeed g (F ∘ δ) t) ≤ K * ‖y - x‖ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      ((M04.continuous_pathSpeed g hpath).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) hspeed
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h
  calc
    g.edist (F x) (F y) ≤ ENNReal.ofReal (K * ‖y - x‖) :=
      hdist.trans (ENNReal.ofReal_le_ofReal hint)
    _ = ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := by
      rw [ENNReal.ofReal_mul' (norm_nonneg _), norm_sub_rev]



theorem exists_disk_lipschitz_constant (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : LoopDisk,
      g.edist (F x.val) (F y.val) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖x.val - y.val‖ := by
  obtain ⟨K, hK, hD⟩ := exists_disk_derivative_bound g hF
  exact ⟨K, hK, fun x y => disk_edist_le_of_derivative_bound g hF hD x.property y.property⟩

end PoincareConjecture.Proofs.M58
