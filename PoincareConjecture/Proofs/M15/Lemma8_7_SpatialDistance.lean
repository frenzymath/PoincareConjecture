import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.Riemannian.PathELength









set_option autoImplicit false

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M15




theorem edist_le_of_tangentNorm_mfderivWithin_le
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    {gamma : ℝ → M} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hgamma : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 gamma (Set.Icc a b))
    (hspeed : ∀ t ∈ Set.Icc a b,
      g.tangentNorm (gamma t)
        (mfderivWithin 𝓘(ℝ) (𝓡 n) gamma (Set.Icc a b) t 1) ≤ C) :
    g.edist (gamma a) (gamma b) ≤ ENNReal.ofReal (C * (b - a)) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  change riemannianEDist (𝓡 n) (gamma a) (gamma b) ≤ _
  apply (riemannianEDist_le_pathELength hgamma rfl rfl hab).trans
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ _ in Icc a b, ENNReal.ofReal C := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hspeed t ht)
    _ = ENNReal.ofReal (C * (b - a)) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        ← ENNReal.ofReal_mul hC]

end PoincareConjecture.Proofs.M15
