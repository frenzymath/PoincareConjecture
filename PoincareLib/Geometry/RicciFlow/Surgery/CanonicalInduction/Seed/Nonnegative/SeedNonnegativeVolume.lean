import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Volume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.VolumeBoundary
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.LocalVolume

/-!
# The exact cubic volume ratio on a nonnegative Ricci ball

The verified local comparison at curvature parameter zero has the
Euclidean model ratio. The actual compact ball supplies confinement.
Source: Morgan--Tian Theorem 1.34, p. 19, and Uniform Seed, pp. 392-393.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.Proofs.M47

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Nonnegative actual Ricci on a compact outer ball retains its cubic
volume density at every smaller positive radius, including equality. -/
theorem seed_nonnegative_ball_volume
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (q : M)
    {R s k : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R)
    (hcompact : IsCompact (closure (g.ball q R)))
    (hRic : ∀ x ∈ g.ball q R, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ D.ricci x v v)
    (hvolume : ENNReal.ofReal (k * R ^ 3) ≤ calibratedMetricVolume g (g.ball q R)) :
    ENNReal.ofReal (k * s ^ 3) ≤ calibratedMetricVolume g (g.ball q s) := by
  rw [M15.calibratedMetricVolume_eq_volumeMeasure] at hvolume ⊢
  have hcompare := M46.canonical_smallBall_volume_at_boundary g q
    (by norm_num : 1 ≤ (3 : ℕ)) (by norm_num : (0 : ℝ) ≤ 0) hs hsR hcompact D
    (fun x hx v => by simpa only [mul_zero, neg_zero, zero_mul] using hRic x hx v)
  have hmodel : (RiemannianMetric.modelVolume 3 0 s /
      RiemannianMetric.modelVolume 3 0 R) * (k * R ^ 3) = k * s ^ 3 := by
    rw [RiemannianMetric.modelVolume_zero_curvature (by norm_num : 1 ≤ (3 : ℕ)),
      RiemannianMetric.modelVolume_zero_curvature (by norm_num : 1 ≤ (3 : ℕ))]
    field_simp [(RiemannianMetric.euclideanUnitBallVolume_pos 3).ne', hR.ne']
  have hposR := RiemannianMetric.modelVolume_pos
    (by norm_num : 1 ≤ (3 : ℕ)) (by norm_num : (0 : ℝ) ≤ 0) hR
  have hposS := RiemannianMetric.modelVolume_pos
    (by norm_num : 1 ≤ (3 : ℕ)) (by norm_num : (0 : ℝ) ≤ 0) hs
  rw [← hmodel, ENNReal.ofReal_mul (div_nonneg hposS.le hposR.le),
    ENNReal.ofReal_div_of_pos hposR]
  exact (mul_le_mul_right hvolume _).trans hcompare

end PoincareMT.Proofs.M47
