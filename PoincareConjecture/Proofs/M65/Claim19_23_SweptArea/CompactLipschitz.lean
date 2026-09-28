import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.PlaneMapRegularity
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65Edist_le_of_derivative_bound (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    {domain : Set LoopPlane} (hconvex : Convex ℝ domain) {K : ℝ}
    (hD : ∀ z ∈ domain, ∀ v : LoopPlane,
      g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z v) ≤ K * ‖v‖)
    {x y : LoopPlane} (hx : x ∈ domain) (hy : y ∈ domain) :
    g.edist (f x) (f y) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let delta : ℝ → LoopPlane := AffineMap.lineMap x y
  have hd : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 delta := (AffineMap.contDiff_lineMap x y).contMDiff
  have hpath : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (f ∘ delta) := hf.comp hd
  have hdvelocity (t : ℝ) : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) delta t 1 = y - x := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).deriv
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1, M04.pathSpeed g (f ∘ delta) t ≤ K * ‖y - x‖ := by
    intro t ht
    have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ delta) t 1 =
        mfderiv (𝓡 2) (𝓡 n) f (delta t) (y - x) := by
      rw [mfderiv_comp_apply t (hf.mdifferentiableAt one_ne_zero)
        (hd.mdifferentiableAt one_ne_zero), hdvelocity]
    dsimp only [M04.pathSpeed]
    rw [hvelocity]
    exact hD (delta t) (hconvex.lineMap_mem hx hy ht) (y - x)
  have hdist : g.edist (f x) (f y) ≤ g.pathELength (f ∘ delta) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpath.contMDiffOn
      (by simp [delta]) (by simp [delta]) zero_le_one
  rw [M04.pathELength_eq_ofReal_integral_pathSpeed g hpath zero_le_one] at hdist
  have hint : (∫ t in (0 : ℝ)..1, M04.pathSpeed g (f ∘ delta) t) ≤ K * ‖y - x‖ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      ((M04.continuous_pathSpeed g hpath).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) hspeed
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using h
  calc
    g.edist (f x) (f y) ≤ ENNReal.ofReal (K * ‖y - x‖) :=
      hdist.trans (ENNReal.ofReal_le_ofReal hint)
    _ = ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := by
      rw [ENNReal.ofReal_mul' (norm_nonneg _), norm_sub_rev]

theorem m65Exists_compact_lipschitz_constant (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    {domain : Set LoopPlane} (hcompact : IsCompact domain) (hconvex : Convex ℝ domain) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : domain,
      g.edist (f x) (f y) ≤ ENNReal.ofReal K * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  obtain ⟨K, hK, hD⟩ := m65Exists_compact_derivative_bound g hf hcompact
  exact ⟨K, hK, fun x y => m65Edist_le_of_derivative_bound g hf hconvex hD x.2 y.2⟩

end PoincareConjecture
