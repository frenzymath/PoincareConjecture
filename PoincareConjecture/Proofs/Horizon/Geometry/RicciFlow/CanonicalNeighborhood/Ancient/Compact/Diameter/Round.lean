import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [ConnectedSpace M]

theorem round_metricDiameter_mul_sqrt_scalar_le
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hround : ConstantPositiveSectionalCurvature g D) (p : M) :
    metricDiameter g Set.univ * Real.sqrt (D.scalarCurvature p) ≤ 10 := by
  obtain ⟨c, hc, hsec⟩ := hround
  have hRic (x : M) (v : TangentSpace (𝓡 3) x) :
      2 * c * g.inner x v v ≤ D.ricci x v v := by
    rw [D.ricci_of_constant_sectional x c
      (D.sectionalCurvature_eq_of_orthonormal x c (hsec x))]
    norm_num
  have hscalar : D.scalarCurvature p = 6 * c := by
    rw [D.scalarCurvature_of_constant_sectional p c
      (D.sectionalCurvature_eq_of_orthonormal p c (hsec p))]
    norm_num
  have hs : 0 < Real.sqrt (D.scalarCurvature p) :=
    Real.sqrt_pos.mpr (by rw [hscalar]; positivity)
  have hsq : (Real.sqrt (D.scalarCurvature p)) ^ 2 = 6 * c := by
    rw [Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hs)), hscalar]
  have hdist (x y : M) :
      (g.edist x y).toReal ≤ 10 / Real.sqrt (D.scalarCurvature p) := by
    apply (le_div_iff₀ hs).mpr
    have hMyers := g.ricci_mul_edist_sq_le D hcomplete hRic x y
    norm_num at hMyers
    have hprod : ((g.edist x y).toReal * Real.sqrt (D.scalarCurvature p)) ^ 2 ≤ 90 := by
      rw [mul_pow, hsq]
      nlinarith
    nlinarith [sq_nonneg ((g.edist x y).toReal * Real.sqrt (D.scalarCurvature p) - 10)]
  apply (le_div_iff₀ hs).mp
  apply csSup_le
  · exact ⟨(g.edist p p).toReal, ⟨(⟨p, Set.mem_univ p⟩,
      ⟨p, Set.mem_univ p⟩), rfl⟩⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hdist x y

end PoincareConjecture
