import PoincareLib.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareLib.Geometry.RicciFlow.Pinching.Bounds
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.CurvatureDefect.NegativeDefect

/-!
# Full curvature bounds from scalar curvature and negative defect

Morgan--Tian Corollary 4.33, p. 80, converts scalar and least-eigenvalue
control into full curvature control. The retained M05 spectral identities
use the frozen four-covariant Hilbert-Schmidt norm and give the conservative
factor 13. Theorem 5.33, pp. 99--100, supplies eventual negative-defect
control, with a full-curvature coefficient independent of its tolerance.

See `proof-work/tasks/M30/derivations/scalar-defect-curvature.md` for the
reviewed source contract and its use in Theorem 11.1, p. 270.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M30

/-- A common scalar and negative-sectional bound controls the actual full
curvature norm, without a nonnegative curvature operator assumption
(Morgan--Tian Corollary 4.33, p. 80). -/
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

/-- The scalar and negative defect at one actual generalized-flow point
control its frozen full-curvature norm (Morgan--Tian Corollary 4.33, p. 80). -/
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

/-- A scalar bound gives simultaneous eventual curvature and negative-defect
bounds, with a full-curvature coefficient independent of the defect tolerance
(Morgan--Tian Theorem 5.33, pp. 99--100, and Corollary 4.33, p. 80). -/
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

end PoincareMT.M30
