import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Bounds
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M30.Thm5_33.NegativeDefect

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

theorem curvatureTensorNorm_le_of_scalar_negativeDefect_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    {K : ℝ} (hK : 0 ≤ K)
    (hR : D.scalarCurvature x ≤ K)
    (hX : D.negativeCurvaturePart x ≤ K) :
    |D.curvatureTensorNorm x| ≤ 13 * K := by
  obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_spectrum hD x
  have hneg : -k3 ≤ K := by
    have hleastBound : -D.leastSectionalCurvature x ≤ K :=
      (le_max_left _ _).trans hX
    simpa only [hleast] using hleastBound
  rw [abs_of_nonneg (show 0 ≤ D.curvatureTensorNorm x from Real.sqrt_nonneg _)]
  exact Poincare.fullNorm_le_of_orderedSpectrum (R₀ := K)
    h12 h23 hscalar hnorm hR le_rfl hK (by linarith)

theorem generalized_curvatureNorm_le_of_scalar_negativeDefect_le
    (hC : RicciFlowCurvatureTheory.{u})
    (F : GeneralizedRicciFlowData.{u}) (p : F.point)
    {K : ℝ} (hK : 0 ≤ K)
    (hR : F.scalar p ≤ K)
    (hX : (F.connection p.1).negativeCurvaturePart p.2 ≤ K) :
    |F.curvatureNorm p| ≤ 13 * K := by
  exact curvatureTensorNorm_le_of_scalar_negativeDefect_le (F.connection p.1)
    (hC.tensor_calculus 3 (F.slice p.1).carrier (F.metric p.1) (F.connection p.1))
    p.2 hK hR hX

theorem eventually_curvatureNorm_and_negativeDefect_le
    (hC : RicciFlowCurvatureTheory.{u}) (S : GeneralizedBlowupSequence.{u})
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (B : ℝ) (hB : 0 ≤ B) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ k : ℕ in atTop, ∀ t, t ∈ (S.flow k).interval →
      ∀ x : ((S.flow k).slice t).carrier,
        (S.flow k).scalar ⟨t, x⟩ ≤ B * S.scale k →
        |(S.flow k).curvatureNorm ⟨t, x⟩| ≤ (13 * max B 1) * S.scale k ∧
          ((S.flow k).connection t).negativeCurvaturePart x ≤ eta * S.scale k := by
  filter_upwards [eventually_negativeDefect_le S hbranch B hB (min eta 1)
    (lt_min heta zero_lt_one)] with k hk
  intro t ht x hR
  have hQ : 0 < S.scale k := S.base_scalar_pos k
  have hK : 0 ≤ max B 1 * S.scale k :=
    mul_nonneg (zero_le_one.trans (le_max_right B 1)) hQ.le
  have hR' : (S.flow k).scalar ⟨t, x⟩ ≤ max B 1 * S.scale k :=
    hR.trans (mul_le_mul_of_nonneg_right (le_max_left B 1) hQ.le)
  have hX := hk t ht x hR
  have hX' : ((S.flow k).connection t).negativeCurvaturePart x ≤
      max B 1 * S.scale k :=
    hX.trans (mul_le_mul_of_nonneg_right
      ((min_le_right eta 1).trans (le_max_right B 1)) hQ.le)
  refine ⟨?_, hX.trans (mul_le_mul_of_nonneg_right (min_le_left eta 1) hQ.le)⟩
  simpa only [mul_assoc] using
    generalized_curvatureNorm_le_of_scalar_negativeDefect_le hC (S.flow k) ⟨t, x⟩
      hK hR' hX'

end PoincareConjecture.M30
