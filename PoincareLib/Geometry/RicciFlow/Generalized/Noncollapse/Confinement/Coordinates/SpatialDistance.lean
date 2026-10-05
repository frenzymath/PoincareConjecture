import PoincareLib.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Lemma8_7_SpatialDistance.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Closed-interval spatial displacement

Morgan-Tian Claims 8.6-8.7, pp. 173-174. Mathlib's length formula with the
within derivative avoids a smooth extension past the path's endpoints.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-spatial-distance.md`.
-/

set_option autoImplicit false

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.Generalized.Noncollapse

/-- A bound on the selected metric's within-derivative speed bounds
endpoint displacement on the closed interval. This is the length step
in Claims 8.6-8.7, pp. 173-174. -/
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

end PoincareMT.Generalized.Noncollapse
