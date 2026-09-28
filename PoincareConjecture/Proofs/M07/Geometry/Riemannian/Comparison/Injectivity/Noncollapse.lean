import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds














noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem ricci_quadratic_lower_bound_of_curvatureTensorNorm_le
    (D : LeviCivitaData g) (x : M) {K : ℝ}
    (hK : D.curvatureTensorNorm x ≤ K) (v : TangentSpace (𝓡 n) x) :
    -(((n : ℝ) - 1) * K) * g.inner x v v ≤ D.ricci x v v := by
  have h := D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K
    (fun u w => (D.abs_sectionalCurvature_le_curvatureTensorNorm x u w).trans hK) v
  simpa only [neg_mul] using h

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric



def smallerBallVolumeBound (n : ℕ) (K R v s : ℝ) : ℝ :=
  (modelVolume n K s / modelVolume n K R) * v

theorem smallerBallVolumeBound_pos {n : ℕ} {K R v s : ℝ}
    (hn : 1 ≤ n) (hK : 0 ≤ K) (hR : 0 < R) (hv : 0 < v) (hs : 0 < s) :
    0 < smallerBallVolumeBound n K R v s :=
  mul_pos (div_pos (modelVolume_pos hn hK hs) (modelVolume_pos hn hK hR)) hv

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem smallerBall_volume_lower_bound_of_curvatureTensorNorm_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {K R v s : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K) (hR : 0 < R) (hv : 0 < v)
    (hcompact : IsCompact (closure (g.ball p (2 * R))))
    (hcurv : ∀ x ∈ g.ball p (2 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p R))
    (hs : 0 < s) (hsR : s ≤ R) :
    0 < smallerBallVolumeBound n K R v s ∧
      ENNReal.ofReal (smallerBallVolumeBound n K R v s) ≤
        g.volumeMeasure (g.ball p s) := by
  refine ⟨smallerBallVolumeBound_pos hn hK hR hv hs, ?_⟩
  have hRic : ∀ x ∈ g.ball p (2 * R), ∀ w : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * K) * g.inner x w w ≤ D.ricci x w w :=
    fun x hx w => D.ricci_quadratic_lower_bound_of_curvatureTensorNorm_le x (hcurv x hx) w
  have hcompare := g.smallBall_volume_lower_bound_of_precompact_ball p hn
    (by positivity : 0 < 2 * R) hK hcompact D hRic hs hsR (by linarith : R < 2 * R)
  unfold smallerBallVolumeBound
  rw [ENNReal.ofReal_mul (div_nonneg (modelVolume_pos hn hK hs).le
      (modelVolume_pos hn hK hR).le),
    ENNReal.ofReal_div_of_pos (modelVolume_pos hn hK hR)]
  exact (mul_le_mul_right hvol _).trans hcompare

end PoincareConjecture.RiemannianMetric
